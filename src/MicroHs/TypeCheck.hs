-- Copyright 2023-2025 Lennart Augustsson
-- See LICENSE file for full license.
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns -Wno-unused-imports -Wno-unused-do-bind #-}
module MicroHs.TypeCheck(
  typeCheck,
  TModule(..), showTModule,
  GlobTables, emptyGlobTables, mergeGlobTables,
  impossible, impossibleShow,
  mkClassConstructor,
  mkSuperSel,
  setBindings,
  boolPrefix,
  listPrefix,
  ValueExport(..), TypeExport(..),
  Symbols,
  isInstId,
  showValueExport, showTypeExport, showTypeExportAssocs,
  ) where
import qualified Prelude(); import MHSPrelude
import Control.Applicative
import Control.Monad
import qualified Data.ByteString.Char8 as BS
import Data.Char
import Data.Function
import Data.List
import Data.Maybe
import MicroHs.Builtin
import MicroHs.Deriving
import MicroHs.Error(MhsError(MhsTypeError))
import MicroHs.Expr
import MicroHs.Fixity
import MicroHs.Flags
import MicroHs.Graph
import MicroHs.Ident
import qualified MicroHs.IdentMap as M
import qualified MicroHs.IntMap as IM
import MicroHs.List
import MicroHs.Names
import MicroHs.Lex(readInt)
import MicroHs.Parse(dotDotIdent)
import MicroHs.SymTab
import MicroHs.TCMonad
import Text.PrettyPrint.HughesPJLiteClass
import Debug.Trace

--primitiveKinds :: [String]
--primitiveKinds = [nameType, nameConstraint, nameSymbol, nameNat]

maxTuple :: Int
maxTuple = 15

deriveClassTypeable :: Bool
deriveClassTypeable = True

----------------------

-- Certain data structures persist during the entire compilation
-- session.  The information is needed beyond the scope where it was defined.
data GlobTables = GlobTables {
  gSynTable   :: SynTable,        -- type synonyms are needed for expansion
  gDataTable  :: DataTable,       -- data/newtype definitions
  gClassTable :: ClassTable,      -- classes are needed for superclass expansion etc
  gInstInfo   :: InstTable        -- instances are implicitely global
  }

instance NFData GlobTables where
  rnf (GlobTables a b c d) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d

emptyGlobTables :: GlobTables
emptyGlobTables = GlobTables { gSynTable = M.empty, gDataTable = M.fromList dataTuples, gClassTable = M.empty, gInstInfo = M.empty }
  -- XXX Could fill the initial symbol table from this
  where dataTuples :: [(Ident, EDef)]
        dataTuples = [ (con, Data (con, map (\ v -> IdKind v eDummy) vs) [Constr [] [] con False (Left $ map (\v-> (False, EVar v)) vs)] [])
                     | n <- 0:[2..15]
                     , let con = tupleConstr noSLoc n
                     , let vs = map (mkIdent . ("a" ++) . show) [1 .. n] ]

mergeGlobTables :: GlobTables -> GlobTables -> GlobTables
mergeGlobTables g1 g2 =
  GlobTables { gSynTable = M.mergeWith mergeSynEntry (gSynTable g1) (gSynTable g2),
               gDataTable = M.merge (gDataTable g1) (gDataTable g2),
               gClassTable = M.merge (gClassTable g1) (gClassTable g2),
               gInstInfo = M.mergeWith mergeInstInfo (gInstInfo g1) (gInstInfo g2) }

-- Merging two synonym table entries for the same family concatenates
-- the equations of two open families; anything else keeps the left entry.
-- Open family equations are deduplicated up to eqEType.
mergeSynEntry :: EType -> EType -> EType
mergeSynEntry e1 e2 =
  case (unTFamEntry e1, unTFamEntry e2) of
    (Just (False, ar1, inj1, eqs1), Just (False, ar2, inj2, eqs2)) | ar1 == ar2 ->
      mkTFamEntry False ar1 (combineInj inj1 inj2) (eqs1 ++ filter keep eqs2)
      where keep e
              | length eqs1 > 16 = isNothing (M.lookup (famEqnKey e) keyMap)
              | otherwise = notElemByEq e eqs1
            keyMap = M.fromList [ (famEqnKey e, ()) | e <- eqs1 ]
            famEqnKey (_, ps, r) = mkIdent (unwords (map showExprRaw (r : ps)))
            notElemByEq e es = not (any (eqFamEqn e) es)
            eqFamEqn (_, p1, r1) (_, p2, r2) = length p1 == length p2 &&
                                               and (zipWith eqEType p1 p2) && eqEType r1 r2
    -- Closed families and ordinary synonyms: first definition wins.
    _ -> e1

----------------------------------------
-- Type family encoding inside synTable.
--
-- Ordinary type synonyms are stored as @EForall QExpl vks rhs@.
-- Type/data families are stored as
--   @ETuple (EVar marker : EVar arity : eqnExprs)@
-- where @marker@ is @$TFOpen@ (open/associated family) or @$TFClosed@
-- (closed family), @arity@ is the number of family arguments, and each
-- equation is @EForall QImpl vks (ETuple (rhs : pats))@.
-- This can never collide with an ordinary synonym, which is always
-- an EForall.
tfOpenMarker, tfClosedMarker :: String
tfOpenMarker   = "$TFOpen"
tfClosedMarker = "$TFClosed"

-- Maximum number of rewrite steps when expanding synonyms/families.
famFuel :: Int
famFuel = 200

mkTFamEntry :: Bool -> Int -> [Bool] -> [([Ident], [EType], EType)] -> EType
mkTFamEntry isClosed arity inj eqns =
  ETuple (EVar (mkIdent marker) :
          EVar (mkIdent (show arity)) : map mkEqn eqns)
  where marker | not (or inj) = if isClosed then tfClosedMarker else tfOpenMarker
               | otherwise    = (if isClosed then tfClosedMarker else tfOpenMarker)
                                ++ ":" ++ map (\ b -> if b then '1' else '0') inj
        mkEqn (pvs, pats, rhs) = EForall QImpl (map (`IdKind` EVar dummyIdent) pvs) (ETuple (rhs : pats))

unTFamEntry :: EType -> Maybe (Bool, Int, [Bool], [([Ident], [EType], EType)])
unTFamEntry (ETuple (EVar m : EVar ar : eqnExprs)) = do
  (isClosed, inj) <- case span (/= ':') (unIdent (unQualIdent m)) of
                (s, "") | s == tfClosedMarker -> Just (True, [])
                        | s == tfOpenMarker   -> Just (False, [])
                (s, ':' : bits) | s == tfClosedMarker -> Just (True, map (== '1') bits)
                                | s == tfOpenMarker   -> Just (False, map (== '1') bits)
                _ -> Nothing
  eqns <- mapM unEqn eqnExprs
  let arity = readInt (unIdent (unQualIdent ar))
  return (isClosed, arity, inj, eqns)
  where unEqn (EForall QImpl vks (ETuple (rhs : pats))) = Just (map idKindIdent vks, pats, rhs)
        unEqn _ = Nothing
unTFamEntry _ = Nothing

-- Combine injectivity flags from two entries for the same family:
-- unknown ([]) contributes nothing, otherwise OR position-wise.
combineInj :: [Bool] -> [Bool] -> [Bool]
combineInj [] b = b
combineInj a [] = a
combineInj a b = zipWith (||) a b

-- Promoted data constructors (DataKinds) are identifiers starting with '\''.
isPromotedIdent :: Ident -> Bool
isPromotedIdent i =
  case unIdent (unQualIdent i) of
    ('\'':_) -> True
    _ -> False

-- The promoted counterpart of a data constructor name.
promIdent :: Ident -> Ident
promIdent i = mkIdentSLoc (getSLoc i) ("'" ++ unIdent (unQualIdent i))

-- Promoted lookup key preserving any module qualifier (e.g. M.Pos -> M.'Pos, Pos -> 'Pos).
promLookupIdent :: Ident -> Ident
promLookupIdent i =
  let s = unIdent i
  in case span (/= '.') (reverse s) of
       (rc, '.' : rm) -> mkIdentSLoc (getSLoc i) (reverse rm ++ ".'" ++ reverse rc)
       _              -> promIdent i

-- Canonical promoted identifier from a value-table entry expression,
-- so unqualified and qualified uses elaborate to the defining module's name.
origPromIdent :: Expr -> Ident -> Ident
origPromIdent ce fallback =
  let q = case ce of { ECon c -> conIdent c; EVar v -> v; _ -> fallback }
      s = unIdent q
  in case span (/= '.') (reverse s) of
       (rc, '.' : rm) -> mkIdentSLoc (getSLoc q) (reverse rm ++ ".'" ++ reverse rc)
       _              -> promIdent fallback

-- Kind of a promoted constructor derived from its term-level type:
-- strip foralls and constraints, keep arrows, quantify free type
-- variables at Type, and default leftover unification variables.
promConKind :: EType -> EType
promConKind t = eForall' QExpl (map (`IdKind` sKind) qvs) body
  where body = arrowsToKind (stripForallCtx t)
        qvs = filter (not . isPromotedIdent) (freeTyVars [body])
        stripForallCtx (EForall _ _ t') = stripForallCtx t'
        stripForallCtx t' | Just (_, r) <- getImplies t' = stripForallCtx r
                          | otherwise = t'
        arrowsToKind ty = foldr tArrow res (map cleanArg as)
          where (as, res) = getArrows (cleanKind ty)
        cleanArg a | Just (_, r) <- getImplies a = cleanArg r
                   | otherwise = cleanKind a
        cleanKind t = case t of
          EApp f a -> EApp (cleanKind f) (cleanKind a)
          ETuple ts -> tApps (tupleConstr (getSLoc t) (length ts)) (map cleanKind ts)
          EListish (LList [x]) -> tApp (tList (getSLoc t)) (cleanKind x)
          EListish (LList xs) -> foldr (\ x acc -> EApp (EApp (EVar (mkIdent "Primitives.':")) (cleanKind x)) acc) (EVar (mkIdent "Primitives.'[]")) xs
          EParen x -> cleanKind x
          EOper x its -> cleanKind (foldl (\ acc (op, r) -> EApp (EApp (EVar op) acc) r) x its)
          ESign x k -> ESign (cleanKind x) (cleanKind k)
          EForall b iks x -> EForall b (map (\ (IdKind i k) -> IdKind i (cleanKind k)) iks) (cleanKind x)
          EUVar _ -> kType
          _ -> t

-- A pattern head that matches only identical rigid constructors.
isRigidConHead :: SynTable -> Ident -> Bool
isRigidConHead syns h = (isConIdent h || isPromotedIdent h) && not (isFamCon syns h)

-- Is the identifier the name of a type/data family?
isTypeFam :: Ident -> T Bool
isTypeFam i = do
  syns <- gets synTable
  return (isFamCon syns i)

-- Is this type a stuck family application (family head, fully applied)?
isStuckFamApp :: SynTable -> EType -> Maybe (Ident, [EType])
isStuckFamApp syns t =
  case getAppM t of
    Just (h, as@(_:_)) | isFamCon syns h -> Just (h, as)
    _ -> Nothing

data MatchResult
  = MatchSubst [(Ident, EType)]
  | MatchApart
  | MatchMaybe
  deriving (Show)

-- 3-valued matching of family arguments against one equation's patterns.
-- patVars are the equation's pattern variables; rigid constructors
-- (including promoted constructors and literals) must match exactly;
-- a rigid/skolem type variable in the arguments facing a constructor
-- pattern is MatchMaybe (it could be instantiated by callers);
-- unification variables and stuck family applications block (MatchMaybe).
matchFamEqn :: SynTable -> [Ident] -> [EType] -> [EType] -> MatchResult
matchFamEqn syns pvs pats args
  | length pats /= length args = MatchApart
  | otherwise = foldl' combine (MatchSubst []) (zipWith (matchOne syns pvs) pats args)
  where combine MatchApart _ = MatchApart
        combine _ MatchApart = MatchApart
        combine MatchMaybe _ = MatchMaybe
        combine _ MatchMaybe = MatchMaybe
        combine (MatchSubst s1) (MatchSubst s2) = mergeSub s1 s2
        mergeSub s1 s2 = foldl' ins (MatchSubst s1) s2
        ins MatchApart _ = MatchApart
        ins MatchMaybe _ = MatchMaybe
        ins (MatchSubst acc) (v, t)
          | Just t' <- lookup v acc =
              if normFam t `eqEType` normFam t' then MatchSubst acc
              else if apartTypes t t' then MatchApart
              else MatchMaybe
          | otherwise = MatchSubst ((v, t) : acc)
        -- Nonlinear variables with apart instances count as apart.
        normFam t = expandSyn' syns t
        apartTypes a b =
          case (getAppM (normFam a), getAppM (normFam b)) of
            (Just (ha, _), Just (hb, _)) -> ha /= hb && isRigidConHead syns ha && isRigidConHead syns hb
            _ -> False

-- Match a single pattern against an argument.
matchOne :: SynTable -> [Ident] -> EType -> EType -> MatchResult
matchOne syns pvs pat arg =
  case patN of
    EVar v | v `elem` pvs -> MatchSubst [(v, argN)]
           | otherwise ->
      -- rigid type variable / nullary constructor facing argument
      case argN of
        EVar v' | v == v' -> MatchSubst []
        EUVar _ -> MatchMaybe
        EVar v' | isRigidConHead syns v && isRigidConHead syns v' -> MatchApart
                | otherwise -> MatchMaybe
        _ | isRigidConHead syns v ->
              case getAppM argN of
                Just (h, _) | h == v -> MatchSubst []
                            | isFamCon syns h -> MatchMaybe
                            | isRigidConHead syns h -> MatchApart
                            | otherwise -> MatchMaybe
                _ -> MatchMaybe
          | otherwise -> MatchMaybe
    EApp _ _ ->
      case argN of
        EUVar _ -> MatchMaybe
        EVar _ -> MatchMaybe  -- rigid variable vs constructor application
        EApp _ _ ->
          case (getAppM patN, getAppM argN) of
            (Just (ph, pas), Just (ah, aas))
              | ph /= ah ->
                 if isFamCon syns ph || isFamCon syns ah then MatchMaybe
                 else if isRigidConHead syns ph && isRigidConHead syns ah then MatchApart
                 else MatchMaybe
              | length pas /= length aas -> MatchApart
              | otherwise -> matchFamEqn syns pvs pas aas
            _ -> MatchMaybe
        _ -> MatchMaybe
    ELit _ l ->
      case argN of
        ELit _ l' | l == l' -> MatchSubst []
                  | otherwise -> MatchApart
        _ | isBlockedArg argN -> MatchMaybe
          | otherwise -> MatchApart
    ETuple ps ->
      case argN of
        ETuple as | length ps == length as -> matchFamEqn syns pvs ps as
        _ | isBlockedArg argN -> MatchMaybe
          | otherwise -> MatchApart
    EListish (LList [p]) ->
      case argN of
        EListish (LList [a]) -> matchFamEqn syns pvs [p] [a]
        _ | isBlockedArg argN -> MatchMaybe
          | otherwise -> MatchApart
    EForall _ _ _ -> MatchMaybe
    ESign t _ -> matchOne syns pvs t arg
    EParen t -> matchOne syns pvs t arg
    _ -> MatchMaybe
  where patN = expandSyn' syns pat
        argN = expandSyn' syns arg
        -- An argument blocks matching when it is a unification variable,
        -- a rigid type variable, or a stuck family application.
        isBlockedArg a =
          case a of
            EUVar _ -> True
            EVar v -> not (isConIdent v) || isFamCon syns v
            _ -> case getAppM a of
                   Just (h, _) -> isFamCon syns h
                   Nothing -> True

-- Is this head a stuck (unreducible) family application head?
isFamCon :: SynTable -> Ident -> Bool
isFamCon syns h = case M.lookup h syns of
                    Just e | Just _ <- unTFamEntry e -> True
                    _ -> False

type Symbols = (SymTab, SymTab)

data TModule a = TModule {
  tModuleName :: IdentModule,     -- module names
  tFixDefs    :: [FixDef],        -- all fixities, exported or not
  tTypeExps   :: [TypeExport],    -- exported types
  tValueExps  :: [ValueExport],   -- exported values (including from T(..))
  tDefaults   :: Defaults,        -- exported defaults
  tBindingsOf :: a                -- bindings
  }
--  deriving (Show)

instance NFData a => NFData (TModule a) where
  rnf (TModule a b c d e f) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e `seq` rnf f

setBindings :: TModule b -> a -> TModule a
setBindings (TModule x y z w v _) a = TModule x y z w v a

type FixDef = (Ident, Fixity)

type Sigma = EType
type Rho   = EType

typeCheck :: Flags -> GlobTables -> ImpType -> [(ImportSpec, TModule a)] -> EModule -> (TModule [EDef], GlobTables, Symbols, TCState)
typeCheck flags globs impt aimps (EModule mn exps defs) =
--  trace (unlines $ map (showTModuleExps . snd) aimps) $
  let
    imps = map filterImports aimps
    tc =
      case defs of
        SetTCState tcs : _ -> xTCStateToTCState tcs  -- hack to set the saved TCState
        _ -> mkTCState mn globs imps
  in case tcRun (tcDefs flags impt defs) tc of
       (tds, tcs) ->
         let
           thisMdl = (mn, mkTModule tds tcs)
           impMdls = [(fromMaybe m mm, tm) | (ImportSpec _ _ m mm _, tm) <- imps]
           allMdls = thisMdl : impMdls
           (texps, vexps) =
             let tys = typeTable tcs; vals = valueTable tcs; ast = assocTable tcs in
             unzip $ map (getTVExps impMap tys vals ast) (gatherAssoc tys vals ast exps)
             where impMap = M.fromListWith (++) [(i, [m]) | (i, m) <- allMdls]
           fexps = map (tFixDefs . snd) allMdls
           sexps = synTable tcs
           dexps = dataTable tcs
           iexps = instTable tcs
           ctbl  = classTable tcs
           dflts = M.fromList $ filter ((`elem` ds) . fst) $ M.toList $ defaults tcs
                 where ds = [ tyQIdent $ expLookup ti (typeTable tcs) | ExpDefault ti <- exps ]
         in  ( tModule mn (nubBy ((==) `on` fst) (concat fexps)) (mergeTypeExports (concat texps)) (concat vexps) dflts tds
             , GlobTables { gSynTable = sexps, gDataTable = dexps, gClassTable = ctbl, gInstInfo = iexps }
             , (typeTable tcs, valueTable tcs)
             , tcs
             )

mergeTypeExports :: [TypeExport] -> [TypeExport]
mergeTypeExports tes =
  let keyTE (TypeExport i (Entry expr _) _) = mkIdent (unIdent i ++ "\0" ++ showExprRaw expr)
      step (m, order) te@(TypeExport _ _ ves) =
        let k = keyTE te
        in case M.lookup k m of
             Nothing -> (M.insert k (te, [ves]) m, k : order)
             Just (te0, vess) -> (M.insert k (te0, vess ++ [ves]) m, order)
      (m, order) = foldl' step (M.empty, []) tes
      get k = case M.lookup k m of
                Just (TypeExport i e _, vess) -> TypeExport i e (foldl' mergeVEExport [] vess)
                Nothing -> impossible
  in map get (reverse order)

-- IdentMap-deduplicated union of value exports, replacing O(N^2) unionBy eqVE.
mergeVEExport :: [ValueExport] -> [ValueExport] -> [ValueExport]
mergeVEExport xs ys = dedupVE veExportKey (xs ++ ys)

-- IdentMap-deduplicated union of associated values, replacing O(N^2) unionBy eqVE.
mergeVEAssoc :: [ValueExport] -> [ValueExport] -> [ValueExport]
mergeVEAssoc xs ys = dedupVE veAssocKey (xs ++ ys)

veExportKey :: ValueExport -> Ident
veExportKey (ValueExport x (Entry expr _)) = mkIdent (unIdent x ++ "\0" ++ showExprRaw expr)

veAssocKey :: ValueExport -> Ident
veAssocKey (ValueExport _ (Entry expr _)) =
  case expr of
    EVar i -> i
    _      -> mkIdent (showExprRaw expr)

dedupVE :: (ValueExport -> Ident) -> [ValueExport] -> [ValueExport]
dedupVE key = go M.empty
  where go _ [] = []
        go seen (ve:ves) =
          let k = key ve
          in if isJust (M.lookup k seen) then go seen ves
             else ve : go (M.insert k () seen) ves

-- A hack to force evaluation of errors.
-- This should be redone to all happen in the T monad.
tModule :: IdentModule -> [FixDef] -> [TypeExport] -> [ValueExport] -> Defaults -> [EDef] ->
           TModule [EDef]
tModule mn fs ts vs ds bs =
--  trace ("tmodule " ++ showIdent mn ++ ":\n" ++ show vs) $
  tseq ts `seq` vseq vs `seq` ds `seq` TModule mn fs ts vs ds bs
  where
    tseq [] = ()
    tseq (TypeExport _ e _:xs) = e `seq` tseq xs
    vseq [] = ()
    vseq (ValueExport _ e:xs) = e `seq` vseq xs

filterImports :: forall a . (ImportSpec, TModule a) -> (ImportSpec, TModule a)
filterImports it@(ImportSpec _ _ _ _ Nothing, _) = it
filterImports (imp@(ImportSpec _ _ _ _ (Just (hide, is))), TModule mn fx ts vs ds a) =
  let
    keep x xs = elem x xs /= hide
    ivs  = [ i | ImpValue i <- is ]
    vs'  = filter (\ (ValueExport i _) -> keep i ivs) vs ++
           if hide then []
           else [ ve | TypeExport _ _ ves <- ts, ve@(ValueExport i _) <- ves, i `elem` ivs ]
    aits = [ i | ImpTypeAll i <- is ]         -- all T(..) imports
    its  = [ i | ImpTypeSome i _ <- is ] ++ aits
    -- Hide the type name, but not all it's parts.
    -- Processing the TypeExport to extract the constructors/fields/methods/defaultmethods
    -- is done later in mkTCState, so we can't remove the export.
    -- To hide it we use a hack: make the identifier inaccessible by prepending a ' '.
    mkTypeExport _ _ [] = []  -- no parts left, just throw away.
    mkTypeExport i e ves = [TypeExport (hideIdent i) e ves] -- hide the type name, keep the associated values
    ts' =
      if hide then
        let ok xs (ValueExport i _) =
              i `notElem` ivs && i `notElem` xs &&
              maybe True (\ f -> f `notElem` xs && f `notElem` its) (unAssocTypeId i) in
        [ TypeExport i e (filter (ok []) ves) | TypeExport i e ves <- ts, i `notElem` its ] ++   -- no hiding of these types, but maybe fields
        [ r | TypeExport i e ves <- ts, ImpTypeSome i' xs <- is, i == i', r <- mkTypeExport i e (filter (ok xs) ves) ]
      else
        let ok xs (ValueExport i _) =
              i `elem` ivs || i `elem` xs || isDefaultMethodId i ||
              maybe False (\ f -> f `elem` its || f `elem` xs) (unAssocTypeId i) in
        [ TypeExport i e                 ves  | TypeExport i e ves <- ts, i `elem` aits ] ++
        [ TypeExport i e (filter (ok xs) ves) | TypeExport i e ves <- ts, ImpTypeSome i' xs <- is, i == i' ]
    allVs = map (\ (ValueExport i _) -> i) vs ++
            concatMap (\ (TypeExport _ _ xvs) -> map (\ (ValueExport i _) -> i) xvs) ts
    allTs = map (\ (TypeExport i _ _) -> i) ts
  in
    (if hide then
       id -- don't complain about missing hidden identifiers; we use it for compatibility
     else
       checkBad (ivs `deleteAlls` allVs) .
       checkBad (its `deleteAlls` allTs))
    (imp, TModule mn fx ts' vs' ds a)

checkBad :: forall a . [Ident] -> a -> a
checkBad [] a = a
checkBad (i:_) _ =
  errorMessage (getSLoc i) $ "not exported: " ++ showIdent i

-- When eporting a data type the associated selectors can be exported
-- with the type or not.  E.g.
--   module M(T, a) where data T = T { a :: Int }
-- behaves the same as
--   module M(T(a)) ...
-- So for each type export item we gather up the associated selectors and add them.
gatherAssoc :: TypeTable -> ValueTable -> AssocTable -> [ExportItem] -> [ExportItem]
gatherAssoc tys vals ast exps =
  let vs = [ i | ExpValue i <- exps ]
      ts = [ ti | ExpTypeSome ti [] <- exps ]
      gather :: ExportItem -> ExportItem
      gather (ExpTypeSome ti is) | is /= [dotDotIdent] =
        let rawAssc = getAssocs ast $ tyQIdent $ expLookup ti tys
            asscV = [ i | ValueExport i ve <- rawAssc, not (isAssocTypeId i), Right ve' <- [stLookup "" i vals], ve' == ve ]
            asscT = [ f | ValueExport ai te <- rawAssc, Just f <- [unAssocTypeId ai], Right te' <- [stLookup "" f tys], te' == te ]
            xs = ((asscV `intersect` vs) ++ (asscT `intersect` ts)) \\ is
        in  ExpTypeSome ti (xs ++ is)
      gather e = e
  in  map gather exps

-- Type and value exports
getTVExps :: forall a . M.Map [TModule a] -> TypeTable -> ValueTable -> AssocTable -> ExportItem ->
             ([TypeExport], [ValueExport])
getTVExps impMap _ _ _ (ExpModule m) =
  -- Export all modules with name m
  case M.lookup m impMap of
    Just ms ->
      case unzip [ (te, ve) | TModule _ _ te ve _ _ <- ms ] of
        (tes, ves) -> (concat tes, concat ves)
    _ -> errorMessage (getSLoc m) $ "undefined module: " ++ showIdent m
getTVExps _ tys vals ast (ExpTypeSome ti is) =
  let e = expLookup ti tys
      assc = getAssocs ast $ tyQIdent e   -- all associated values (and tagged associated types)
      ves = concatMap one is
      one i | i == dotDotIdent = assc          -- '..' means all associated values & types
            | otherwise =
              case filter (\ (ValueExport i' _) -> i == i' || isDefaultMethodOfId i i' || isAssocTypeOfId i i') assc of
                es@(_:_) -> es                 -- Pick the associated value/type if it exists
                [] -> [ValueExport (unQualIdent i) $ expLookup i vals]
                                               -- otherwise, just look up a pattern synonym.
                                               -- This might accidentally pick up a constructor from
                                               -- another type, but it doesn't really matter.
      assocTes =
        [ TypeExport famId ae (getAssocs ast (tyQIdent ae))
        | ValueExport ai ae <- ves
        , Just famId <- [unAssocTypeId ai]
        ]
  in (TypeExport (unQualIdent ti) e ves : assocTes, [])

getTVExps _ _ vals _ (ExpValue i) = ([], [ValueExport (unQualIdent i) (expLookup i vals)])
getTVExps _ _ _ _ (ExpDefault _) = ([], [])

expLookup :: Ident -> SymTab -> Entry
expLookup i m = either throw id $ stLookup "export" i m

tyQIdent :: Entry -> Ident
tyQIdent (Entry (EVar qi) _) = qi
tyQIdent _ = error "tyQIdent"

eVarI :: SLoc -> String -> Expr
eVarI loc = EVar . mkIdentSLoc loc

-- Construct a dummy TModule for the currently compiled module.
-- It has all the relevant export tables.
-- The value&type export tables will later be filtered through the export list.
mkTModule :: forall a . HasCallStack => [EDef] -> TCState -> TModule a
mkTModule tds tcs =
  let
    mn = moduleName tcs
    tt = typeTable  tcs
    at = assocTable tcs
    vt = valueTable tcs

    -- Find the Entry for a type.
    tentry i =
      case stLookup "" (qualIdent mn i) tt of
        Right e -> e
        _       -> impossible
    ventry i t =
      let qi = qualIdent mn i in
      case stLookup "" qi vt of
        Right e -> e
        _       -> Entry (EVar qi) t  -- XXX A hack for boot modules

    -- Find all value Entry for names associated with a type.
    assoc i = getAssocs at (qualIdent mn i)

    -- All top level values possible to export.
    ves = [ ValueExport i (ventry i t') | Sign is t <- tds, let t' = expandSyn' st t, i <- is ] ++
          [ ValueExport i (ventry i t') | ForImp _ _ qi t <- tds, let t' = expandSyn' st t, let i = unQualIdent qi ]
      where st = synTable tcs

    -- All top level types possible to export.
    -- Type/data families are exported like types; data-instance
    -- constructors/selectors are attached to the family in assocTable.
    tes =
      [ TypeExport i (tentry i) (assoc i) | Data    (i, _) _ _ <- tds ] ++
      [ TypeExport i (tentry i) (assoc i) | Newtype (i, _) _ _ <- tds ] ++
      [ TypeExport i (tentry i) (assoc i) | Class _ (i, _) _ _ <- tds ] ++
      [ TypeExport i (tentry i) []        | Type    (i, _) _   <- tds ] ++
      [ TypeExport i (tentry i) (assoc i) | TypeFam (i, _) _ _ _ <- tds ] ++
      [ TypeExport i (tentry i) (assoc i) | DataFam (i, _) _   <- tds ]

    -- All fixity declaration.
    fes = [ (qualIdent mn i, fx) | Infix fx is <- tds, i <- is ]

    -- All defaults
    des = defaults tcs

  in  TModule mn fes tes ves des impossible

-- Find all value Entry for names associated with a type.
-- XXX join stLookup code with tentry
getAssocs :: (HasCallStack) => AssocTable -> Ident -> [ValueExport]
getAssocs at ai = fromMaybe [] $ M.lookup ai at

mkTCState :: IdentModule -> GlobTables -> [(ImportSpec, TModule a)] -> TCState
mkTCState mdlName globs mdls =
  let
    allValues :: ValueTable
    allValues =
      let
        usyms (ImportSpec _ qual _ _ _, TModule _ _ tes ves _ _) =
          if qual then [] else
          [ (i, [e]) | ValueExport i e    <- ves, not (isInstId i)  ] ++
          [ (i, [e]) | TypeExport  _ _ cs <- tes, ValueExport i e <- cs, not (isDefaultMethodId i), not (isAssocTypeId i) ]
        qsyms (ImportSpec _ _ _ mas _, TModule mn _ tes ves _ _) =
          let m = fromMaybe mn mas in
          [ (v, [e]) | ValueExport i e    <- ves,                        let { v = qualIdent    m i } ] ++
          [ (v, [e]) | TypeExport  _ _ cs <- tes, ValueExport i e <- cs, not (isAssocTypeId i), let { v = qualIdentD e m i } ] ++
          [ (v, [Entry (EVar v) t]) | (i, ClassInfo _ _ t _ _) <- M.toList (gClassTable globs), let { v = mkClassConstructor i } ]
        -- Default methods are always entered with their qualified original name.
        qualIdentD (Entry e _) m i | not (isDefaultMethodId i) = qualIdent m i
                                   | otherwise =
                                     case e of
                                       EVar qi -> qi
                                       _ -> undefined
      in stFromList (concatMap usyms mdls) (concatMap qsyms mdls)
    allTypes :: TypeTable
    allTypes =
      let
        usyms (ImportSpec _ qual _ _ _, TModule _ _ tes _ _ _) =
          if qual then [] else
          [ (i, [e])  | TypeExport i e _   <- tes, not (isHiddenIdent i) ] ++
          [ (f, [ae]) | TypeExport _ _ cs <- tes, ValueExport ai ae <- cs, Just f <- [unAssocTypeId ai] ]
        qsyms (ImportSpec _ _ _ mas _, TModule mn _ tes _ _ _) =
          let m = fromMaybe mn mas in
          [ (qualIdent m i, [e])  | TypeExport i e _   <- tes, not (isHiddenIdent i) ] ++
          [ (qualIdent m f, [ae]) | TypeExport _ _ cs <- tes, ValueExport ai ae <- cs, Just f <- [unAssocTypeId ai] ]
        -- DataKinds: promoted constructors are visible as types.
        promUsyms (ImportSpec _ qual _ _ _, TModule _ _ tes _ _ _) =
          if qual then [] else
          [ (p, [Entry (EVar (origPromIdent ce i)) (promConKind t)])
          | TypeExport _ _ cs <- tes,
            ValueExport i (Entry ce t) <- cs,
            not (isPromotedIdent i), not (isAssocTypeId i), isConIdent i,
            let p = promIdent i ]
        promQsyms (ImportSpec _ _ _ mas _, TModule mn _ tes _ _ _) =
          let m = fromMaybe mn mas in
          [ (qualIdent m p, [Entry (EVar (origPromIdent ce i)) (promConKind t)])
          | TypeExport _ _ cs <- tes,
            ValueExport i (Entry ce t) <- cs,
            not (isPromotedIdent i), not (isAssocTypeId i), isConIdent i,
            let p = promIdent i ]
      in stFromList (concatMap usyms mdls ++ concatMap promUsyms mdls)
                    (concatMap qsyms mdls ++ concatMap promQsyms mdls)

    allFixes :: FixTable
    allFixes = M.fromList (concatMap (tFixDefs . snd) mdls)
    allAssocs :: AssocTable
    allAssocs =
      let assocs (_, TModule _ _ tes _ _ _) = [ (tyQIdent e, cs) | TypeExport _ e cs <- tes ]
      in  M.fromListWith mergeVEAssoc $ concatMap assocs mdls

    dflts = foldr (mergeDefaults . tDefaults . snd) M.empty mdls

    primPromotedTypes :: [(Ident, [Entry])]
    primPromotedTypes =
      [ (p, [Entry (EVar p) (promConKind t)])
      | (i, es) <- primValues, Entry _ t <- es,
        not (isPromotedIdent i), isConIdent i,
        let p = promIdent i ]
  in TC { moduleName = mdlName,
          unique = 1,
          fixTable = addPrimFixs allFixes,
          typeTable = foldr (uncurry stInsertGlbA) allTypes (primTypes ++ primPromotedTypes),
          synTable = gSynTable globs,
          dataTable = gDataTable globs,
          valueTable = foldr (uncurry stInsertGlbA) allValues primValues,
          assocTable = allAssocs,
          uvarSubst = IM.empty,
          tcMode = TCExpr,
          classTable = gClassTable globs,
          ctxTables = (gInstInfo globs, [], [], []),
          constraints = [],
          defaults = dflts,
          famEqTable = [],
          impEqTable = M.empty,
          savedTypeTable = stEmpty
        }

mergeDefaults :: Defaults -> Defaults -> Defaults
mergeDefaults ds = foldr (uncurry $ M.insertWith mrg) ds . M.toList
  where mrg :: [EType] -> [EType] -> [EType]
        mrg ts ts' | all (\ t -> elemBy eqEType t ts) ts' = ts
                   | any (\ t -> elemBy eqEType t ts') ts = ts'
                   | otherwise = []  -- If neither module's default subsumes the other
                                     -- then use empty defaults, as per spec.

mergeInstInfo :: InstInfo -> InstInfo -> InstInfo
mergeInstInfo (InstInfo m1 l1 fds) (InstInfo m2 l2 _) =
  let
    m = foldr (uncurry $ M.insertWith mrg) m2 (M.toList m1)
    mrg e1@(EVar i1) (EVar i2)
      | i1 == i2  = e1
      | otherwise = errorMessage (getSLoc i1) $ "Multiple instances: " ++ showSLoc (getSLoc i2)
    mrg e1 _e2 = e1 -- XXX improve this
    l = mergeInstDicts l1 l2
  in  InstInfo m l fds

-- Approximate equality for dictionaries.
-- The important thing is to avoid exact duplicates in the instance table.
eqInstDict :: InstDict -> InstDict -> Bool
eqInstDict (InstDict e _) (InstDict e' _) = eqExpr e e'

instDictKey :: InstDict -> Ident
instDictKey (InstDict (EVar i) _) = i
instDictKey (InstDict e _)        = mkIdent (showExprRaw e)

mergeInstDicts :: [InstDict] -> [InstDict] -> [InstDict]
mergeInstDicts [] l2 = l2
mergeInstDicts l1 [] = l1
mergeInstDicts [d1] l2 =
  let k1 = instDictKey d1
  in if any (\d2 -> instDictKey d2 == k1) l2 then l2 else d1 : l2
mergeInstDicts l1 [d2] =
  let k2 = instDictKey d2
  in if any (\d1 -> instDictKey d1 == k2) l1 then l1 else l1 ++ [d2]
mergeInstDicts l1 l2 =
  let go _ [] = []
      go seen (d:ds) =
        let k = instDictKey d
        in if isJust (M.lookup k seen) then go seen ds
           else d : go (M.insert k () seen) ds
  in go M.empty (l1 ++ l2)

-- Identifier should only be seen with it's qualified name.
isInstId :: Ident -> Bool
isInstId i = (instPrefix ++ uniqIdentSep) `isPrefixOf` unIdent i

mkInstId :: SLoc -> EType -> Ident
mkInstId loc ct = mkIdentSLoc loc $ instPrefix ++ uniqIdentSep ++ clsTy
  where clsTy = map (\ c -> if isSpace c then '@' else c) $ showExprRaw ct

--------------------------

-- Use the type table as the value table, and the primKind table as the type table.
withTypeTable :: forall a . T a -> T a
withTypeTable ta = do
  otcm <- gets tcMode
  vt <- gets valueTable
  tt <- gets typeTable
  st <- gets savedTypeTable
  when (otcm == TCType) $
    modify $ \ ts -> ts { savedTypeTable = vt }
  putValueTable tt            -- use type table as value table
  let
    tcm = succ otcm
    next = case tcm of { TCType -> primKindTable; TCKind -> primSortTable; _ -> undefined }
  putTypeTable next           -- use kind/sort table as type table
  putTCMode tcm
  a <- ta
  tt' <- gets valueTable
  putValueTable vt
  putTypeTable (if otcm == TCExpr then tt' else tt)
  modify $ \ ts -> ts { savedTypeTable = st }
  putTCMode otcm
  return a

addAssocTable :: Ident -> [ValueExport] -> T ()
addAssocTable i ids = modify $ \ ts -> ts { assocTable = M.insert i ids (assocTable ts) }

addClassTable :: Ident -> ClassInfo -> T ()
addClassTable i x = modify $ \ ts -> ts { classTable = M.insert i x (classTable ts) }

addInstTable :: [InstDictC] -> T ()
addInstTable ics = do
--  tcTrace $ "addInstTable: " ++ show ics
  let
    -- Change type variable to unique unification variables.
    freshSubst u iks =
      -- XXX
      -- [u ..] is not portable between 64 and 32 bit since it uses
      -- maxBound::Int which will differ between them.
      -- XXX Using a function in InstInfo is not ideal.
      zipWith (\ ik j -> (idKindIdent ik, EUVar j)) iks [u .. 100000000::Int]

    mkInstInfo :: InstDictC -> T (Ident, InstInfo)
    mkInstInfo (e, iks, ctx, ct, fds) = do
      case (iks, ctx, getApp ct) of
        ([], [], (c, [EVar i])) -> return (c, InstInfo (M.singleton i e) [] fds)
        (_,  _,  (c, ts      )) -> return (c, InstInfo M.empty [InstDict e ii] fds)
          where ii u =
                  let ctx' = map (subst s) ctx
                      ts'  = map (subst s) ts
                      s    = freshSubst u iks
                  in  (ctx', ts')
  iis <- mapM mkInstInfo ics
  it <- gets instTable
  -- Group the new instances by class first, so each class merges only once.
  let grouped = M.fromListWith mergeInstInfo iis
  putInstTable $ M.mergeWith mergeInstInfo grouped it

-- Generate a dictionary for the constraint.
-- Reuse old dictionaries if possible.
newDict :: SLoc -> EConstraint -> T Expr
newDict loc ctx = do
  ctx' <- derefUVar ctx
  cs <- gets constraints
  -- Check if there's already an identical constraint.
  case find (\ (_, c) -> eqEType c ctx') cs of
    Just (i, _) -> do
--      traceM ("newDict reuse: " ++ show (i, ctx'))
      return (EVar i)
    _ -> do
      i <- newDictIdent loc
--      traceM ("newDict: " ++ show (i, ctx', length cs))
      addConstraint i ctx'
      return (EVar i)

addConstraint :: Ident -> EConstraint -> T ()
addConstraint d ctx = do
--  tcTrace $ "addConstraint: " ++ showIdent d ++ " :: " ++ showEType ctx
  eqs <- gets typeEqTable
  feqs <- gets famEqTable
  unless (null eqs && null feqs) $
    modify $ \ ts -> ts { impEqTable = M.insert d (eqs, feqs) (impEqTable ts) }
  modify $ \ ts -> ts{ constraints = (d, ctx) : constraints ts }

withDicts :: forall a . HasCallStack => [(Ident, EConstraint)] -> T a -> T a
withDicts ds ta = do
--  tcTrace $ "+++ withDicts enter " ++ show ds
  ct <- gets ctxTables
  feqs <- gets famEqTable
  mapM_ addDict ds
  a <- ta
  putCtxTables ct
  putFamEqTable feqs
--  tcTrace $ "--- withDicts leave " ++ show ds
  return a

withDict :: forall a . HasCallStack => Ident -> EConstraint -> T a -> T a
withDict i c ta = do
--  tcTrace $ "+++ withDict enter " ++ show (i, c)
  ct <- gets ctxTables
  feqs <- gets famEqTable
  addDict (i, c)
  a <- ta
  putCtxTables ct
  putFamEqTable feqs
--  tcTrace $ "--- withDict leave " ++ show (i, c)
  return a

normConstraint :: EConstraint -> T EConstraint
normConstraint c = do
  c0 <- derefUVar c
  eqs <- gets typeEqTable
  c1 <- expandSynSoft (normTypeEq eqs c0)
  if null eqs then return c1 else do
    let c1' = normTypeEq eqs c1
    if c1' `eqEType` c1 then return c1' else normTypeEq eqs <$> expandSynSoft c1'

addDict :: HasCallStack => (Ident, EConstraint) -> T ()
addDict (i, c) = do
  c' <- normConstraint c
  if null (metaTvs [c']) then
    addInstDict i c'
   else
    -- With constraint variables we might get unification variables.
    -- We stash them away in hope that we will learn more later.
    addMetaDict i c'

addInstDict :: HasCallStack => Ident -> EConstraint -> T ()
addInstDict di c = do
  ics <- expandDict (EVar di) c
  -- Type equalities are handled differently.
  let addeq [] = return []
      addeq ((_, _, _, EApp (EApp (EVar eq) t1) t2, _):is) | eq == identTypeEq = do addEqDict t1 t2; addeq is
      addeq (i:is) = (i :) <$> addeq is
      normIC (e, vks, ctx, cc, fds) = do
        ctx' <- mapM normConstraint ctx
        cc'  <- normConstraint cc
        return (e, vks, ctx', cc', fds)
  ics' <- addeq ics
  ics'' <- mapM normIC ics'
  c'' <- normConstraint c
  addInstTable ics''
  addArgDict di c''

addEqDict :: HasCallStack => EType -> EType -> T ()
addEqDict t1 t2 = do
  syns <- gets synTable
  a <- expandSynSoft t1
  b <- expandSynSoft t2
  -- Equalities with a stuck family application head cannot be recorded
  -- in the TypeEqTable (which only handles variable-headed rules), so
  -- they go into the famEqTable instead; expandSyn' then rewrites them.
  -- A bare (non-constructor) type variable on the other side is still
  -- handled by the TypeEqTable, which orients var -> rhs, UNLESS that
  -- variable occurs inside the stuck family application (e.g. b ~ Body b p),
  -- where var -> rhs would loop and orienting F args -> var terminates.
  case (famSide syns a, famSide syns b) of
    _ | a `eqEType` b -> return ()
    (True, _) | not (isBareTyVar b) || any (eqEType b) (subTerms a) -> recordFamEq a b
    (_, True) | not (isBareTyVar a) || any (eqEType a) (subTerms b) -> recordFamEq b a
    _ -> do
      is <- gets typeEqTable
      putTypeEqTable (addTypeEq syns a b is)
  where famSide syns t = isJust (isStuckFamApp syns t) ||
                         case t of EVar h -> isFamCon syns h; _ -> False
        isBareTyVar (EVar v) = not (isConIdent v)
        isBareTyVar _ = False

-- Record a given equality with a stuck family application on the left.
-- Oriented larger/family-headed F args -> rhs; skipped when the left
-- side occurs in the right side (to avoid rewrite cycles) or when it
-- is already recorded.
recordFamEq :: EType -> EType -> T ()
recordFamEq lhs rhs = do
  feqs <- gets famEqTable
  let occurs = any (eqEType lhs) (subTerms rhs)
      dup = any (\(l, r) -> l `eqEType` lhs && r `eqEType` rhs) feqs
  unless (occurs || dup) $
    addFamEq (lhs, rhs)

-- All subterms of a type, including itself.
subTerms :: EType -> [EType]
subTerms t =
  t : case t of
        EApp f a -> subTerms f ++ subTerms a
        ETuple ts -> concatMap subTerms ts
        EListish (LList ts) -> concatMap subTerms ts
        EOper t its -> subTerms t ++ concatMap (subTerms . snd) its
        ESign t _ -> subTerms t
        EParen t -> subTerms t
        EForall _ _ t -> subTerms t
        _ -> []

addMetaDict :: HasCallStack => Ident -> EConstraint -> T ()
addMetaDict i c = do
  ms <- gets metaTable
  putMetaTable ((i,c) : ms)

addArgDict :: HasCallStack => Ident -> EConstraint -> T ()
addArgDict i c = do
  ads <- gets argDicts
  putArgDicts ((i,c) : ads)

addPrimFixs :: FixTable -> FixTable
addPrimFixs =
  M.insert (mkIdent "Primitives.->") (AssocRight, -1) .
  M.insert (mkIdent "Primitives.=>") (AssocRight, -2)

-- r for 'realm', suggested by ChatGPT
rSort :: ESort
rSort = EVar (mkIdent "Primitives.Sort")

sKindKindKind :: EKind
sKindKindKind = sArrow sKind (sArrow sKind sKind)

kTypeTypeS :: EType
kTypeTypeS = kArrow kType kType

kTypeTypeTypeS :: EType
kTypeTypeTypeS = kArrow kType $ kArrow kType kType

-- E.g.
--  Kind :: Sort
primSortTable :: KindTable
primSortTable =
  let
    entry i s = Entry (EVar (mkIdentB i)) s
    qsorts = [
       -- The kinds are wired in (for now)
       (mkIdentB nameKind,       [entry nameKind rSort])
       ]
  in stFromList (map (first unQualIdent) qsorts) qsorts

-- E.g.
--  Type       :: Kind
--  Constraint :: Kind
--  (->)       :: Kind -> Kind -> Kind
primKindTable :: KindTable
primKindTable =
  let
    entry i k = Entry (EVar (mkIdentB i)) k
    qkinds = [
       -- The kinds are wired in (for now)
       (mkIdentB nameType,       [entry nameType sKind]),
       (mkIdentB nameConstraint, [entry nameConstraint sKind]),
       (mkIdentB nameSymbol,     [entry nameSymbol sKind]),
       (mkIdentB nameNat,        [entry nameNat sKind]),
       (identArrow,              [entry nameArrow sKindKindKind])
       ]
  in stFromList (map (first unQualIdent) qkinds) qkinds

-- E.g.
--  Bool  :: Type
--  Int   :: Type
--  (->)  :: Type -> Type -> Type
--  (=>)  :: forall k . Constraint -> k -> k
--  Maybe :: Type -> Type
primTypes :: [(Ident, [Entry])]
primTypes =
  let
    entry i = Entry (EVar i)
    k = mkIdent "k"
    kv = EVar k
    kk = IdKind k sKind
    -- Tuples are polykinded since they need to handle both Type and Constraint
    -- (,) :: forall k . k -> k -> k
    -- etc.
    tuple n =
      let
        i = tupleConstr builtinLoc n
      in  (i, [entry i $ EForall QExpl [kk] $ foldr kArrow kv (replicate n kv)])
    -- (=>) :: forall k . Constraint -> k -> k
    kImplies = EForall QExpl [kk] $ kConstraint `kArrow` (kv `kArrow` kv)
    -- (~) :: forall k . k -> k -> Constraint
    kTypeEqual = EForall QExpl [kk] $ kv `kArrow` (kv `kArrow` kConstraint)
  in
      [
       -- The function arrow et al are bothersome to define in Primitives, so keep them here.
       -- The fixity is set by addPrimFixs
       (mkIdentB "->",           [entry identArrow    kTypeTypeTypeS]),
       (mkIdentB "=>",           [entry identImplies  kImplies]),
       (mkIdentB "~",            [entry identTypeEq   kTypeEqual]),
       -- Primitives.hs uses the type [], and it's annoying to fix that.
       -- XXX should not be needed
       (identList,               [entry identList     kTypeTypeS]),
       (mkIdentB "[]",           [entry identList     kTypeTypeS]),
       (mkIdentB "\x2192",       [entry identArrow    kTypeTypeTypeS]),  -- ->
       (mkIdentB "\x21d2",       [entry identImplies  kImplies])         -- =>
      ] ++
      map tuple (0 : enumFromTo 2 maxTuple)

-- E.g.
--  True :: Bool
--  (&&) :: Bool -> Bool
--  Just :: forall a . a -> Maybe a
--  ,    :: forall a b . a -> b -> (a,b)
primValues :: [(Ident, [Entry])]
primValues =
  let
    idk i = IdKind (mkIdent ("a" ++ show (i::Int))) kType
    tuple n =
      let
        c = tupleConstr builtinLoc n
        vks = [idk i | i <- enumFromTo 1 n]
        ts = map tVarK vks
        r = tApps c ts
      in  (c, [Entry (ECon $ ConData [(c, n)] c []) $ EForall QExpl vks $ EForall QExpl [] $ foldr tArrow r ts ])
    tyCons = EForall QExpl [ka] $ EForall QExpl [] $ a `tArrow` la `tArrow` la
    tyNil = EForall QExpl [ka] $ EForall QExpl [] la
    ka = idk 1
    a = tVarK ka
    la = tApp (EVar identList) a
  in  [(mkIdentB ":",  [Entry conCons tyCons])
      ,(mkIdentB "[]", [Entry conNil  tyNil])] ++
      map tuple (0 : enumFromTo 2 maxTuple)

kArrow :: EKind -> EKind -> EKind
kArrow = tArrow

sArrow :: ESort -> ESort -> ESort
sArrow = tArrow

setUVar :: TRef -> EType -> T ()
setUVar r1 (EUVar r2) | r1 <= r2 = error "setUVar"
setUVar i t = modify $ \ ts -> ts{ uvarSubst = IM.insert i t (uvarSubst ts) }

getUVar :: Int -> T (Maybe EType)
getUVar i = gets (IM.lookup i . uvarSubst)

munify :: HasCallStack =>
          SLoc -> Expected -> EType -> T ()
munify loc (Infer r) b = tSetRefType loc r b
munify loc (Check a) b = unify loc b a

-- Expand type synonyms, but keep location info
expandSynLoc :: EType -> T EType
expandSynLoc at = setSLocExpr (getSLoc at) <$> expandSyn at

-- Synonyms are expanded after kind checking.
-- There should be no synonyms in any of the symbol tables (except synTable).
expandSyn :: HasCallStack =>
             EType -> T EType
--expandSyn at | trace ("expandSyn: " ++ show at) False = undefined
expandSyn at = do
  rt <- expandSynSoft at
  syns <- gets synTable
  let -- Check that there are no unexpanded synonyms left.
      -- Stuck family applications (whose head is in synTable) are fine.
      chk (EApp f a) = do chk f; chk a
      chk (EVar i) =
        case M.lookup i syns of
          Nothing -> return ()
          Just e | Just _ <- unTFamEntry e -> return ()
                 | otherwise -> tcError (getSLoc i) $ "bad synonym use: " ++ showIdent i ++ " in " ++ showEType at
      chk (EUVar _) = return ()
      chk (EForall _ _ t) = chk t
      chk (ELit _ _) = return ()
      chk (ETuple ts) = mapM_ chk ts
      chk (EListish (LList ts)) = mapM_ chk ts
      chk (EOper t its) = chk t >> mapM_ (chk . snd) its
      chk (EParen t) = chk t
      chk (ESign t _) = chk t
      chk (EQVar _ t) = chk t
      chk (ECon _) = return ()
      chk _ = impossible
  chk rt
  return rt

-- Expand synonyms, reduce type families, and rewrite with given
-- family equalities, without the bad-synonym check.
-- Safe to use during unification and constraint solving.
expandSynSoft :: HasCallStack => EType -> T EType
expandSynSoft at = do
  syns <- gets synTable
  feqs <- gets famEqTable
  return (expandSynFull syns feqs at)

-- Pure backbone of expandSynSoft: expand/reduce, rewrite with the
-- given family equalities, and repeat until a fixpoint (bounded by fuel,
-- and stopping on rewrite cycles so contradictory givens cannot loop).
expandSynFull :: HasCallStack => SynTable -> [(EType, EType)] -> EType -> EType
expandSynFull syns [] t = expandSyn' syns t
expandSynFull syns feqs t = loop famFuel [] t
  where loop 0 _ t = t
        loop n seen t =
          let t' = rewriteFamEq feqs (expandSyn' syns t)
          in if t' `eqEType` t || any (eqEType t') seen then t'
             else loop (n - 1) (t : seen) t'

-- Rewrite stuck family applications using given equalities
-- (exact match up to eqEType, bottom-up).
rewriteFamEq :: [(EType, EType)] -> EType -> EType
rewriteFamEq [] t = t
rewriteFamEq feqs t = go t
  where go t0 =
          let t1 = case t0 of
                     EApp f a -> EApp (go f) (go a)
                     ETuple ts -> ETuple (map go ts)
                     EListish (LList ts) -> EListish (LList (map go ts))
                     EOper t its -> EOper (go t) (map (second go) its)
                     ESign t k -> ESign (go t) k
                     EParen t -> EParen (go t)
                     EForall b iks t -> EForall b iks (go t)
                     _ -> t0
          in case [ rhs | (lhs, rhs) <- feqs, lhs `eqEType` t1 ] of
               (rhs:_) -> rhs
               [] -> t1

expandSynNoChk :: HasCallStack =>
                  EType -> T EType
expandSynNoChk t = do
  syns <- gets synTable
  return $ expandSyn' syns t

-- Expand with the given synonym table.
-- Apartness-aware type family reduction happens here:
-- open families reduce on the first matching equation, closed families
-- only reduce when all earlier equations are apart, and a blocked
-- (MatchMaybe) equation leaves the application stuck.
expandSyn' :: HasCallStack =>
              SynTable -> EType -> EType
expandSyn' syns = esyn
  where
    esyn = syn famFuel []
    -- Expand synonyms that have enough arguments
    syn fuel ts t =
      case t of
        EApp f a -> syn fuel (syn fuel [] a : ts) f
        EVar i ->
          case M.lookup i syns of
            Nothing -> eApps t ts
            Just entry | Just (isClosed, arity, _, eqns) <- unTFamEntry entry ->
              if length ts < arity then
                eApps t ts  -- under-applied: stuck
              else
                let (famArgs, extraArgs) = splitAt arity ts
                in case reduceFam syns fuel i isClosed eqns famArgs of
                     Just rhs -> syn (fuel - 1) extraArgs rhs
                     Nothing -> eApps t ts  -- stuck
            Just (EForall _ vks tt) ->
              if fuel <= 0 then eApps t ts
              else
                let is = map idKindIdent vks
                    s = zip is ts
                    lis = length is
                    lts = length ts
                in  if lis > lts then
                      eApps t ts
                    else
                      -- Too few arguments, just leave it alone
                      syn (fuel - 1) (drop lis ts) (subst s tt)
            Just _ -> impossible
        EUVar _ -> eApps t ts
        ESign a _ -> syn fuel ts a   -- Throw away signatures, they don't affect unification
        EForall b iks tt | null ts -> EForall b iks (syn fuel [] tt)
        ELit _ (LStr _) -> eApps t ts
        ELit _ (LInteger _) -> eApps t ts
        ETuple ts' | null ts -> ETuple (map (syn fuel []) ts')
        EListish (LList [x]) | null ts -> EListish (LList [syn fuel [] x])
        EOper t1 its | null ts -> EOper (syn fuel [] t1) (map (second (syn fuel [])) its)
        EParen t1 | null ts -> syn fuel ts t1
        EQVar _ _ -> eApps t ts
        ECon _ -> eApps t ts
        _ -> impossiblePP t

-- Try to reduce one fully-applied family application.
-- Returns Nothing when the application is stuck.
reduceFam :: SynTable -> Int -> Ident -> Bool -> [([Ident], [EType], EType)] -> [EType] -> Maybe EType
reduceFam _ fuel _ _ _ _ | fuel <= 0 = Nothing
reduceFam syns _ _ False eqns famArgs = goOpen eqns
  where goOpen [] = Nothing
        goOpen ((pvs, pats, rhs) : rest) =
          case matchFamEqn syns pvs pats famArgs of
            MatchSubst s -> Just (subst s rhs)
            _ -> goOpen rest
reduceFam syns _ _ True eqns famArgs = goClosed True eqns
  where goClosed _ [] = Nothing
        goClosed allApart ((pvs, pats, rhs) : rest) =
          case matchFamEqn syns pvs pats famArgs of
            MatchSubst s | allApart -> Just (subst s rhs)
                         | otherwise -> Nothing
            MatchApart -> goClosed allApart rest
            MatchMaybe -> Nothing


mapEType :: (EType -> EType) -> EType -> EType
mapEType fn = rec
  where
    rec (EApp f a) = EApp (rec f) (rec a)
    rec (ESign t k) = ESign (rec t) k
    rec (EForall b iks t) = EForall b iks (rec t)
    rec t = fn t

derefUVar :: EType -> T EType
derefUVar at =
  case at of
    EApp f a -> do
      fx <- derefUVar f
      ax <- derefUVar a
      return $ EApp fx ax
    EUVar i -> do
      mt <- getUVar i
      case mt of
        Nothing -> return at
        Just t -> do
          t' <- derefUVar t
          setUVar i t'
          return t'
    EVar _ -> return at
    ESign t k -> ESign <$> derefUVar t <*> derefUVar k
    ETuple ts -> ETuple <$> mapM derefUVar ts
    EListish (LList ts) -> (EListish . LList) <$> mapM derefUVar ts
    EParen t -> EParen <$> derefUVar t
    EOper t ies -> EOper <$> derefUVar t <*> mapM (\ (i, e) -> (,) i <$> derefUVar e) ies
    EQVar _ _ -> return at
    EForall b iks t -> EForall b <$> iks' <*> derefUVar t
      where iks' = mapM (\ (IdKind i k) -> IdKind i <$> derefUVar k) iks
    ELit _ (LStr _) -> return at
    ELit _ (LInteger _) -> return at
    _ -> impossible

tcErrorTK :: HasCallStack =>
             SLoc -> String -> T ()
tcErrorTK loc msg = do
  tcm <- gets tcMode
  tcError loc $ msgTCMode' tcm ++ ": " ++ msg

-- For error messages
msgTCMode :: TCMode -> String
msgTCMode TCExpr = "value"
msgTCMode TCType = "type"
msgTCMode TCKind = "kind"
msgTCMode TCSort = "sort"

msgTCMode' :: TCMode -> String
msgTCMode' TCExpr = "type"
msgTCMode' TCType = "kind"
msgTCMode' TCKind = "sort"
msgTCMode' TCSort = "realm"

-- The convention is  unify loc actual expected.
-- The original pair is carried along so that a mismatch deep inside
-- a type is reported in terms of the whole types.
unify :: HasCallStack =>
         SLoc -> EType -> EType -> T ()
unify loc a b = unifyR loc (a, b) a b

type Orig = (EType, EType)   -- (actual, expected) as given to unify

unifyR :: HasCallStack =>
          SLoc -> Orig -> EType -> EType -> T ()
unifyR _   _ (EVar x1)    (EVar x2)      | x1 == x2  = return ()
unifyR loc o t1@(EApp _ _) t2@(EApp _ _) = do
  syns <- gets synTable
  -- Never structurally decompose an application whose head is a
  -- stuck type/data family: F a ~ G b must not unify F ~ G and a ~ b,
  -- and F a ~ Int cannot decompose EApp vs EVar.
  if famHeaded syns t1 || famHeaded syns t2
    then unifySlow loc o t1 t2
    else case (t1, t2) of
           (EApp f1 a1, EApp f2 a2) -> do { unifyR loc o f1 f2; unifyR loc o a1 a2 }
           _ -> impossible
unifyR loc o t1@(EUVar r1) t2@(EUVar r2) | r1 < r2   = unifyVar loc o r2 t1   -- always make higher
                                         | r1 > r2   = unifyVar loc o r1 t2   --   TRefs point to lower
                                         | otherwise = return ()
unifyR loc o (EUVar r1)   t2                         = unifyVar loc o r1 t2
unifyR loc o t1           (EUVar r2)                 = unifyVar loc o r2 t1
unifyR loc o t1           t2                         = unifySlow loc o t1 t2

-- Head identifier of a type application, if it has one.
appHeadIdent :: EType -> Maybe Ident
appHeadIdent (EApp f _) = appHeadIdent f
appHeadIdent (ESign t _) = appHeadIdent t
appHeadIdent (EParen t) = appHeadIdent t
appHeadIdent (EVar i) = Just i
appHeadIdent _ = Nothing

-- Is this type headed by a stuck type/data family application?
famHeaded :: SynTable -> EType -> Bool
famHeaded syns t =
  case appHeadIdent t of
    Just h -> isFamCon syns h
    Nothing -> False

-- Slow path: expand synonyms, reduce families, rewrite with given
-- family equalities, and dereference unification variables first.
-- Identical stuck family applications succeed immediately; a stuck
-- family application against anything else is deferred as a type
-- equality constraint so solveEq and given equalities can discharge it.
unifySlow :: HasCallStack =>
             SLoc -> Orig -> EType -> EType -> T ()
unifySlow loc o t1 t2 = do
  syns <- gets synTable
  t1d <- derefUVar t1
  t2d <- derefUVar t2
  t1e <- expandSynSoft t1d
  t2e <- expandSynSoft t2d
  d1 <- derefUVar t1e
  d2 <- derefUVar t2e
  case (d1, d2) of
    _ | d1 `eqEType` d2 -> return ()
    (EUVar r1, _) -> unifyVar loc o r1 d2
    (_, EUVar r2) -> unifyVar loc o r2 d1
    (EVar x1, EVar x2) | x1 == x2 -> return ()
    (EApp f1 a1, EApp f2 a2)
      | not (famHeaded syns d1) && not (famHeaded syns d2) ->
          do { unifyR loc o f1 f2; unifyR loc o a1 a2 }
    _ -> do
      tcm <- gets tcMode
      eqs <- gets typeEqTable
      feqs <- gets famEqTable
      (n1, n2) <- if tcm == TCExpr && (not (null eqs) || not (null feqs))
                  then do
                    c1 <- normConstraint d1 >>= derefUVar
                    c2 <- normConstraint d2 >>= derefUVar
                    return (c1, c2)
                  else return (d1, d2)
      case (n1, n2) of
        _ | n1 `eqEType` n2 -> return ()
        (EUVar r1, _) -> unifyVar loc o r1 n2
        (_, EUVar r2) -> unifyVar loc o r2 n1
        (EVar x1, EVar x2) | x1 == x2 -> return ()
        (EApp f1 a1, EApp f2 a2)
          | not (famHeaded syns n1) && not (famHeaded syns n2) ->
              do { unifyR loc o f1 f2; unifyR loc o a1 a2 }
        _ -> do
          let stuck = famHeaded syns n1 || famHeaded syns n2
          case tcm of
            TCExpr | stuck || not (null eqs) || not (rigidClash n1 n2) -> addEqConstraint loc n1 n2
            _ | stuck -> addEqConstraint loc n1 n2
              | otherwise -> mismatchError loc o

-- Two types with different rigid heads (or arities) can never unify.
-- (Stuck type families are handled before this is consulted: they are
-- never rigidly clashable, so this is only called on family-free types.)
rigidClash :: EType -> EType -> Bool
rigidClash t1 t2 =
  case (getAppM t1, getAppM t2) of
    (Just (c1, as1), Just (c2, as2)) -> c1 /= c2 || length as1 /= length as2
    _                                -> False

mismatchError :: HasCallStack => SLoc -> Orig -> T a
mismatchError loc (actual, expected) = do
  tcm <- gets tcMode
  (a, e) <- niceTypes2 actual expected
  throw $ MhsTypeError loc (msgTCMode' tcm) (showTypeUser a) (showTypeUser e)

unifyVar :: HasCallStack =>
            SLoc -> Orig -> TRef -> EType -> T ()
unifyVar loc o r t = do
  mt <- getUVar r
--  tcTrace $ "unifyVar: " ++ show (r,t)
  case mt of
    Nothing -> unifyUnboundVar loc o r t
    Just t' -> unifyR loc o t' t

-- Unify an unbount tyvar r1 with the type at2
unifyUnboundVar :: HasCallStack =>
                   SLoc -> Orig -> TRef -> EType -> T ()
unifyUnboundVar loc o r1 at2@(EUVar r2) = do
  -- We know r1 /= r2
  mt2 <- getUVar r2
  case mt2 of
    Nothing ->
      -- Both are tyvars.  Always point later tyvars towards earlier ones.
      -- There generaliation step in tcBindGrp relies on this.
      if r1 > r2 then
        setUVar r1 at2
      else
        setUVar r2 (EUVar r1)
    Just t2 -> unifyR loc o (EUVar r1) t2
unifyUnboundVar loc _ r1 t2 = do
  vs <- getMetaTyVars [t2]
  if r1 `elem` vs then do
    (a, b) <- niceTypes2 (EUVar r1) t2
    tcError loc $ "occurs check: cannot construct the infinite type: " ++ showTypeUser a ++ " ~ " ++ showTypeUser b
   else
    setUVar r1 t2

-----------------------------------------
-- Error message support

-- Show a type for the user, with String instead of [Char].
showTypeUser :: EType -> String
showTypeUser = sub . showEType
  where
    sub ('#' : s) | (_:_, r) <- span isDigit s = sub r    -- drop skolem uniques, a#12 shows as a
    sub (c : s) = c : sub s
    sub [] = []

-- Dereference and give unification variables readable names.
niceTypes :: [EType] -> T [EType]
niceTypes ts = do
  ts' <- mapM derefUVar ts
  let vs = nub (concatMap uvarsOf ts')
      used = concatMap allVarsExpr ts'
      names = [ n | n <- map (:[]) ['a'..'z'] ++ [ 't' : show k | k <- [1::Int ..] ], mkIdent n `notElem` used ]
      sub = zip vs names
      go (EUVar i) | Just n <- lookup i sub = EVar (mkIdent n)
      go (EApp f a) = EApp (go f) (go a)
      go (EForall b iks t) = EForall b iks (go t)
      go (ESign t k) = ESign (go t) k
      go t = t
  return (map go ts')

niceTypes2 :: EType -> EType -> T (EType, EType)
niceTypes2 a b = do
  ts <- niceTypes [a, b]
  case ts of
    [a', b'] -> return (a', b')
    _        -> impossible

uvarsOf :: EType -> [Int]
uvarsOf (EUVar i) = [i]
uvarsOf (EApp f a) = uvarsOf f ++ uvarsOf a
uvarsOf (EForall _ _ t) = uvarsOf t
uvarsOf (ESign t _) = uvarsOf t
uvarsOf _ = []

-- Reset unification map
tcReset :: T ()
tcReset = modify $ \ ts -> ts{ uvarSubst = IM.empty }

newUVar :: T EType
newUVar = EUVar <$> newUniq

newIdent :: SLoc -> String -> T Ident
newIdent loc s = do
  u <- newUniq
  return $ mkIdentSLoc loc $ s ++ uniqIdentSep ++ show u

tLookup :: HasCallStack =>
           String -> Ident -> T (Expr, EType)
tLookup msg i = do
  env <- gets valueTable
  case stLookup msg i env of
    Right (Entry e s) -> return (setSLocExpr (getSLoc i) e, s)
    Left            e -> throw e

-- Sort of a kind: maps Type -> Kind, (k1 -> k2) -> (sort(k1) -> sort(k2)).
kindToSort :: EType -> EType
kindToSort (EForall _ _ b) = kindToSort b
kindToSort t | Just (a, b) <- getArrow t = kArrow (kindToSort a) (kindToSort b)
kindToSort _ = sKind

tLookupV :: HasCallStack =>
           Ident -> T (Expr, EType)
tLookupV i = do
  tcm <- gets tcMode
  env <- gets valueTable
  let sloc e = setSLocExpr (getSLoc i) e
  case stLookupST i env of
    STOne (Entry e s) -> return (sloc e, s)
    -- If the identifier is ambiguous we use a pretty gruesome hack:
    -- if there is only one hit that is not a record getter, we use that.
    -- This allows ordinary functions/methods to have the same name as a
    -- field, and they will be preferred.
    STMany es | [Entry e s] <- filter (\ (Entry e' _) -> not (isGetExpr e')) es -> return (sloc e, s)
              | [Entry e s] <- filter isFtpPoly es
              , all (\ ent@(Entry e' _) -> isGetExpr e' || isFtpPoly ent || isFtpMono e') es -> return (sloc e, s)
      where isFtpPoly (Entry (EVar v) _) = any (`isPrefixOf` unIdent v) ["Data.Foldable.", "Data.Traversable.", "Data.Foldable1."]
            isFtpPoly _ = False
            isFtpMono (EVar v) = any (`isPrefixOf` unIdent v) ["Data.List.", "Data.List_Type.", "Control.Monad."]
            isFtpMono _ = False
    STNone | tcm == TCType && not (isPromotedIdent i) && isConIdent i ->
      case stLookupST (promLookupIdent i) env of
        STOne (Entry e s) -> return (sloc e, s)
        STMany es | [Entry e s] <- nub es -> return (sloc e, s)
        _ -> tLookup (msgTCMode tcm) i
    STNone | tcm == TCKind && not (isPromotedIdent i) -> do
      st <- gets savedTypeTable
      case stLookupST i st of
        STOne (Entry e k) -> do
          k' <- derefUVar k >>= expandSyn
          return (sloc e, kindToSort k')
        STMany es | [Entry e k] <- nub es -> do
          k' <- derefUVar k >>= expandSyn
          return (sloc e, kindToSort k')
                  | otherwise -> tLookup (msgTCMode tcm) i
        STNone | not (isConIdent i) ->
          -- Implicit lowercase kind variable (e.g. k in (a :: k)):
          -- treat as a fresh kind variable of sort Kind.
          return (sloc (EVar i), sKind)
               | otherwise -> tLookup (msgTCMode tcm) i
    _ -> tLookup (msgTCMode tcm) i       -- generate the error normally

tInst :: HasCallStack => Expr -> EType -> T (Expr, EType)
--tInst ae t | trace ("tInst: " ++ show (ae, t)) False = undefined
tInst ae (EForall _ vks t) = do
  t' <- tInstForall vks t
  tInst ae t'
tInst ae at | Just (ctx, t) <- getImplies at = do
  --tcTrace $ "tInst: addConstraint: " ++ show ae ++ ", " ++ show d ++ " :: " ++ show ctx
{-
  if eqExpr ae eCannotHappen then
    -- XXX Gruesome hack.  This avoids adding constraints in cases like
    --  (C a => a) -> T `subsCheck` b
    undefined
    --tInst ae t
   else do
-}
    d <- newDict (getSLoc ae) ctx
    tInst (EApp ae d) t
tInst ae at = return (ae, at)

tInstForall :: [IdKind] -> EType -> T EType
tInstForall vks t =
  if null vks then
    return t
  else do
    let vs = map idKindIdent vks
    us <- mapM (const newUVar) vks
    return (subst (zip vs us) t)

tInst' :: EType -> T EType
tInst' (EForall _ vks t) = tInstForall vks t
tInst' t = return t

extValE :: HasCallStack =>
           Ident -> EType -> Expr -> T ()
extValE i t e = do
  venv <- gets valueTable
  putValueTable (stInsertLcl i (Entry e t) venv)

-- Extend the global symbol table with i = e :: t
-- Add both qualified and unqualified versions of i.
extValETop :: HasCallStack =>
              Ident -> EType -> Expr -> T ()
extValETop i t e = do
  mn <- gets moduleName
  venv <- gets valueTable
  t' <- expandSyn t                 -- expand type synonyms before entering the symbol table
--  when (show i == "mkTyCon") $ traceM (show "extValETop " ++ show (i, t, t'))
  let qi = qualIdent mn i
      venv'  = stInsertGlbQ qi [Entry e t'] venv
      venv'' = stInsertGlbU  i [Entry e t'] venv'
  putValueTable venv''

-- Extend symbol table with i::t.
-- The translation for i will be the qualified name.
-- Add both qualified and unqualified versions of i.
extValQTop :: HasCallStack =>
              Ident -> EType -> T ()
extValQTop i t = do
  mn <- gets moduleName
  extValETop i t (EVar (qualIdent mn i))

extVal :: HasCallStack =>
          Ident -> EType -> T ()
extVal i t = extValE i t $ EVar i

extVals :: HasCallStack =>
           [(Ident, EType)] -> T ()
extVals = mapM_ (uncurry extVal)

extTyp :: Ident -> EKind -> T ()
extTyp i k = extTypE i k (EVar i)

extTypE :: Ident -> EKind -> EType -> T ()
extTypE i k t = do
  tenv <- gets typeTable
  putTypeTable (stInsertLcl i (Entry t k) tenv)

extTyps :: [(Ident, EType)] -> T ()
extTyps = mapM_ (uncurry extTyp)

extSyn :: Ident -> [IdKind] -> EType -> T ()
extSyn i iks t = do
  -- Eta reduce type synonyms.
  -- E.g. 'type T a = Maybe a' could be 'type T = Maybe'.
  case etaReduce iks t of
    (iks', t') -> do
      senv <- gets synTable
      putSynTable (M.insert i (EForall QExpl iks' t') senv)

extData :: Ident -> EDef -> T ()
extData i d = do
  denv <- gets dataTable
  putDataTable (M.insert i d denv)

extFix :: Ident -> Fixity -> T ()
extFix i fx = modify $ \ ts -> ts{ fixTable = M.insert i fx (fixTable ts) }

withExtVal :: forall a . HasCallStack =>
              Ident -> EType -> T a -> T a
withExtVal i t ta = do
  venv <- gets valueTable
  extVal i t
  a <- ta
  putValueTable venv
  return a

withExtVals :: forall a . HasCallStack =>
               [(Ident, EType)] -> T a -> T a
withExtVals env ta = do
  venv <- gets valueTable
  extVals env
  a <- ta
  putValueTable venv
  return a

withExtTyps :: forall a . [IdKind] -> T a -> T a
withExtTyps iks ta = do
  let env = [ (v, k) | IdKind v k <- iks, not (isDummyIdent v) ]
  venv <- gets typeTable
  extTyps env
  a <- ta
  putTypeTable venv
  return a

tcDefs :: HasCallStack => Flags -> ImpType -> [EDef] -> T [EDef]
tcDefs flags impt ds = do
  case impt of
    ImpNormal -> pure ()
    ImpBoot ->
      case filter (not . bootExportable) ds of
        d : _ -> tcError (getSLoc d) "not allowed in -boot"
        _ -> pure ()

--  tcTrace ("tcDefs 1:\n" ++ showEDefs ds)
  -- First, add infix declarations so the operators can be resolved
  mapM_ tcAddInfix ds                                 -- collect fixity declarations
  dst <- tcDefsType ds                                -- kind check type definitions
--  tcTrace ("tcDefs 2:\n" ++ showEDefs dst)
  addTypesAndDatas dst                            -- add typedefinitions to the symbol table
  dste <- tcExpandClassInst flags impt dst            -- expand class&instance, do deriving
--  tcTrace ("tcDefs 3:\n" ++ showEDefs dste)
  setDefault dste                                     -- set current defaults
  dste' <- tcDefsValue dste                           -- type check all value definitions
  mapM_ addAssocs dste'
  fixupDataInstAssocs dste'                         -- link data instances to their families
  addClassTypeAssocs ds                             -- link associated type/data families to their classes

  case impt of
    ImpNormal -> do
      return dste'
    ImpBoot ->
      -- remove value definitions
      return $ filter bootExportable dste'

bootExportable :: EDef -> Bool
bootExportable (Fcn _ _) = False
bootExportable (PatBind _ _) = False
bootExportable (Instance _ ms bs) = null ms && null bs
bootExportable StandDeriving{} = False
bootExportable TypeFam{} = True
bootExportable DataFam{} = True
bootExportable _ = True

setDefault :: [EDef] -> T ()
setDefault defs = do
  tys <- gets typeTable
  ds <- sequence [ do { ts' <- mapM expandSyn ts; return (tyQIdent $ expLookup c tys, ts') }
                 | Default (Just c) ts <- defs ]
  dflts <- gets defaults
  let dflts' = foldr (uncurry M.insert) dflts ds
--  traceM $ "Active defaults " ++ show (M.toList dflts')
  putDefaults dflts'

tcAddInfix :: EDef -> T ()
tcAddInfix (Infix fx is) = do
  mn <- gets moduleName
  mapM_ (\ i -> extFix (qualIdent mn i) fx) is
tcAddInfix _ = return ()

-- Kind check type definitions
tcDefsType :: HasCallStack => [EDef] -> T [EDef]
tcDefsType ds = withTypeTable $ do
  let ds0 = extractClassFams ds
  mapM_ (addTypeKind M.empty) ds0
  kindSigs <- getKindSigns ds
  sequence_ [ extValQTop i k | (i, k) <- M.toList kindSigs ]
  ds1 <- concat <$> mapM expandTopDataInst ds0 -- desugar top-level data instances
  dst <- mapM (tcDefType ds1) ds1              -- Kind check all top level type expressions
--  vars <- gets uvarSubst
--  tcTrace $ show vars
  mn <- gets moduleName
  -- Refine non-GADT H98 local promoted constructors with their exact kinds.
  -- Uses the elaborated definitions (constructor argument types already
  -- desugared, so no EListish/ETuple reaches the kind table).
  sequence_
    [ extValQTop (promIdent c)
        (promConKind (dsType (foldr tArrow (tApps (qualIdent mn ti) (map (EVar . idKindIdent) tvks))
                                (map snd (either id (map snd) ets)))))
    | Data (ti, tvks) cs _ <- dst
    , Constr [] [] c _ ets <- cs
    ]
  vt <- gets valueTable
  let ent (Entry i k) = Entry i <$> zonkKindExpr k
  vt' <- mapMSymTab ent vt
  putValueTable vt'
  mapM zonkTypeDef dst    -- make type/class definition LHSs have resolved kinds
--  tcTrace $ "tcDefType value table:\n" ++ show vt'

zonkKindExpr :: EKind -> T EKind
zonkKindExpr k = mapEType def <$> (derefUVar k >>= expandSyn)
  where def (EUVar _) = kType    -- default kind variables to Type
        def t = t

zonkTypeDef :: EDef -> T EDef
zonkTypeDef = go
  where
    zonkVks = mapM (\ (IdKind i k) -> IdKind i <$> zonkKindExpr k)
    zonkEqn (evks, ps, r) = (\ evks' -> (evks', ps, r)) <$> zonkVks evks
    zonkM _ Nothing  = pure Nothing
    zonkM f (Just x) = Just <$> f x
    go (Class ctx (n, vks) ct ms) = Class ctx <$> ((,) n <$> zonkVks vks) <*> pure ct <*> pure ms
    go (Data (n, vks) cs ds)      = Data      <$> ((,) n <$> zonkVks vks) <*> pure cs <*> pure ds
    go (Newtype (n, vks) c ds)    = Newtype   <$> ((,) n <$> zonkVks vks) <*> pure c  <*> pure ds
    go (Type (n, vks) t)          = Type      <$> ((,) n <$> zonkVks vks) <*> pure t
    go (TypeFam (n, vks) mk inj eqs)  = TypeFam <$> ((,) n <$> zonkVks vks) <*> zonkM zonkKindExpr mk <*> pure inj <*> zonkM (mapM zonkEqn) eqs
    go (DataFam (n, vks) mk)      = DataFam   <$> ((,) n <$> zonkVks vks) <*> zonkM zonkKindExpr mk
    go (TypeInst vks q ps r)      = TypeInst  <$> zonkVks vks <*> pure q <*> pure ps <*> pure r
    go d = pure d

-- Get all kind signatures, and do sort checking of them.
getKindSigns :: HasCallStack => [EDef] -> T (M.Map EKind)
getKindSigns ds = do
  let iks = [ (i, k) | KindSign i k <- ds ]
      kind (i, k) = (,) i <$> tcKind (Check sKind) k
  multCheck (map fst iks)
  iks' <- mapM kind iks
  return $ M.fromList iks'

-- Expand class and instance definitions (must be done after type synonym processing).
tcExpandClassInst :: Flags -> ImpType -> [EDef] -> T [EDef]
tcExpandClassInst flags impt dst = do
  dsf <- withTypeTable $ do
    dsc <- concat <$> mapM expandClass dst              -- Expand all class definitions
    concat <$> mapM expandField dsc                     -- Add HasField instances
  mapM_ addValueTypeClass dsf                           -- Add methods, needed while deriving
  dsd <-
    case impt of
      ImpBoot -> return dsf
      ImpNormal -> concat <$> mapM doDeriving dsf       -- Add derived instances
  dumpIf flags Dderive $
    tcTrace' $ "derived:\n" ++ showEDefs dsd
  res <- concat <$> mapM (expandInst dsd) dsd                 -- Expand all instance definitions
  dumpIf flags DexpandInst $
    tcTrace' $ "expanded:\n" ++ showEDefs res
  return res

-- Check&rename the given kinds, also insert the type variables in the symbol table.
withVks :: forall a . HasCallStack => [IdKind] -> ([IdKind] -> T a) -> T a
withVks vks fun = assertTCMode (>=TCType) $ do
  tcm <- gets tcMode
  let
    expect = case tcm of { TCType -> sKind; TCKind -> rSort; _ -> undefined }
    loop r [] = fun (reverse r)
    loop r (IdKind i mk : iks) = do
      -- When we have 'forall k (a :: k) . t' the k is a kind.
      -- Instead we have have to write 'forall (k :: Kind) (a :: k) . t' and then
      -- we have to guess that k needs sort checking.
      -- This doesn't work if there is not exactly 'Kind' (e.g., 'Primitives.Kind')
      -- This sucks.
      if tcm == TCType && guessIsKind mk then do
        s <- withTypeTable $ withTypeTable $ tcExpr (Check rSort) mk
        let ik = IdKind i s
        withExtTyps [ik] $ loop (ik : r) iks
      else do
        k' <- case mk of
                EVar d | d == dummyIdent -> newUVar
                _                        -> withTypeTable $ tcExpr (Check expect) (dsType mk)   -- bump to next level
        withExtVal i k' $ loop (IdKind i k' : r) iks
  loop [] vks

guessIsKind :: EType -> Bool
guessIsKind (EVar i)                      = i == mkIdent "Kind"
guessIsKind t =
  case getArrow t of
    Just (f, a) -> guessIsKind f || guessIsKind a
    _           -> False

-- Add symbol a table entry (with kind) for each top level typeish definition.
-- If there is a kind signature, use it.  If not, use a kind variable.
addTypeKind :: M.Map EKind -> EDef -> T ()
addTypeKind kdefs adef = do
  mn <- gets moduleName
  let
    addDef (i, vks) = do
      k <- case M.lookup i kdefs of
             Just kd -> return kd
             Nothing -> do
               aks <- mapM (const newUVar) vks
               rk  <- newUVar
               return (foldr kArrow rk aks)
      extValQTop i k
    addPromCon ti tvks (Constr ciks _ c _ ets)
      | not (isPromotedIdent c), isConIdent c = do
          let arity = either length length ets
              p = promIdent c
          pk <- if null tvks && null ciks && arity == 0
                then return (EVar (qualIdent mn ti))
                else return (EForall QExpl [IdKind (mkIdent "$pk") sKind] (EVar (mkIdent "$pk")))
          extValQTop p pk
      | otherwise = return ()
  case adef of
    Data    lhs@(ti, tvks) cs _ -> addDef lhs >> mapM_ (addPromCon ti tvks) cs
    Newtype lhs@(ti, tvks) c  _ -> addDef lhs >> addPromCon ti tvks c
    Type    lhs _               -> addDef lhs
    Class _ lhs _ _             -> addDef lhs
    TypeFam lhs _ _ _           -> addDef lhs
    DataFam lhs _               -> addDef lhs
    _                           -> return ()

-- Add symbols associated with a type.
addAssocs :: HasCallStack => EDef -> T ()
addAssocs adef = do
  mn <- gets moduleName
  let
    addAssoc ti is = do
      vt <- gets valueTable
      let val (i, lookupName) =
            case stLookup "" lookupName vt of
              Right e -> [ValueExport i e]
              _       -> []  -- fields with existential type have no selector
      addAssocTable (qualIdent mn ti) (concatMap val is)

    assocData _ (Constr _ _ c _ (Left _)) = [(c, c)]
    -- Keep the visible field name, but look up its owner-specific getter.
    assocData ti (Constr _ _ c _ (Right its)) =
      (c, c) : [ (f, mkGetName ti f) | (f, _) <- its ]

  case adef of
    Data    (i, _) cs _ | not (isMatchDataTypeName i)
                        -> addAssoc i (nub $ concatMap (assocData i) cs)
    Newtype (i, _) c  _ -> addAssoc i (assocData i c)
    Class _ (i, _) _ ms -> addAssoc i [ (x, x) | Sign ns _ <- ms, m <- ns, x <- [m, mkDefaultMethodId m] ]
    _                   -> return ()

-- Copy the constructors and field selectors of each data-instance
-- representation type to its family in the association table, so that
-- @module M (D(..))@ and @import M (D(..))@ export/import data
-- instance constructors and record selectors.
fixupDataInstAssocs :: [EDef] -> T ()
fixupDataInstAssocs ds = do
  at <- gets assocTable
  let fams = [ (qfam, qdf) | TypeInst _ qfam _ rhs <- ds,
                             Just (qdf, _) <- [getAppM rhs],
                             "$DInst$" `isInfixOf` unIdent qdf ]
      addOne table (qfam, qdf) =
        case M.lookup qdf table of
          Nothing -> table
          Just ves -> M.insertWith mergeVEAssoc qfam ves table
  modify $ \ ts -> ts { assocTable = foldl' addOne at fams }

-- Add type synonyms to the synonym table, and data/newtype to the data table.
-- Type families and data families are registered as family entries;
-- type instances append equations to their (open) family's entry.
-- Two phases so instances always find their family regardless of order.
addTypesAndDatas :: [EDef] -> T ()
addTypesAndDatas ds = do
  mapM_ addTypeAndData [ d | d <- ds, not (isTypeInst d) ]
  mapM_ addTypeAndData [ d | d <- ds, isTypeInst d ]
  where isTypeInst TypeInst{} = True
        isTypeInst _ = False

addTypeAndData :: EDef -> T ()
addTypeAndData adef = do
  mn <- gets moduleName
  case adef of
    Type    (i, vs) t  -> extSyn  (qualIdent mn i) vs t
    Data    (i, _) _ _ -> extData (qualIdent mn i) adef
    Newtype (i, _) _ _ -> extData (qualIdent mn i) adef
    TypeFam (i, vks) _ inj meqns -> registerTypeFam mn i vks inj meqns
    DataFam (i, vks) _ -> registerTypeFam mn i vks [] Nothing
    TypeInst vks qfam pats rhs -> registerTypeInst vks qfam pats rhs
    _                  -> return ()

-- Register a type/data family declaration in the synonym table.
registerTypeFam :: IdentModule -> Ident -> [IdKind] -> [Bool] -> Maybe [TypeEqn] -> T ()
registerTypeFam mn i vks inj meqns = do
  let qi = qualIdent mn i
      arity = length vks
      newEntry = case meqns of
        Just es -> mkTFamEntry True arity inj [(map idKindIdent evks, ps, r) | (evks, ps, r) <- es]
        Nothing -> mkTFamEntry False arity inj []
  syns <- gets synTable
  case M.lookup qi syns of
    Nothing -> putSynTable (M.insert qi newEntry syns)
    Just old ->
      case unTFamEntry old of
        Nothing -> tcError (getSLoc i) (showIdent qi ++ " is already defined as a type synonym")
        Just (oldIsClosed, oldArity, oldInj, oldEqns)
          | oldArity /= arity -> tcError (getSLoc i) ("type family arity mismatch for " ++ showIdent qi)
          | otherwise ->
              case meqns of
                -- Re-declaring an open family (e.g. completing a boot
                -- declaration): keep the already-registered equations,
                -- but pick up any newly declared injectivity.
                Nothing ->
                  let inj' = combineInj oldInj inj
                  in when (inj' /= oldInj) $
                       putSynTable (M.insert qi (mkTFamEntry oldIsClosed oldArity inj' oldEqns) syns)
                -- Overwrite when module `mn` is recompiled over a partially
                -- invalidated cache; same-module duplicate declarations are
                -- already rejected by `multCheck` in `addTypeKinds`.
                Just _ -> putSynTable (M.insert qi newEntry syns)

-- Append one equation to an open family's entry.
-- Coincident equations (same LHS up to alpha-renaming of the quantified
-- pattern variables, with an eqEType-equal RHS) register idempotently.
registerTypeInst :: [IdKind] -> Ident -> [EType] -> EType -> T ()
registerTypeInst vks qfam pats rhs = do
  syns <- gets synTable
  case M.lookup qfam syns of
    Nothing -> tcError (getSLoc qfam) ("not a type family: " ++ showIdent qfam)
    Just old ->
      case unTFamEntry old of
        Nothing -> tcError (getSLoc qfam) ("not a type family: " ++ showIdent qfam)
        Just (True, _, _, _) -> tcError (getSLoc qfam) ("cannot add instance for closed type family " ++ showIdent qfam)
        Just (False, arity, oldInj, eqns)
          | length pats /= arity -> tcError (getSLoc qfam) ("wrong arity in instance for " ++ showIdent qfam)
          | any (isCoincident syns) eqns -> return ()
          | any (isDuplicate syns) eqns ->
              tcError (getSLoc qfam) ("duplicate instance for " ++ showIdent qfam)
          | otherwise ->
              putSynTable (M.insert qfam (mkTFamEntry False arity oldInj (eqns ++ [(vs, pats, rhs)])) syns)
  where vs = map idKindIdent vks
        -- Canonicalize quantified pattern variables to positional $n names so
        -- alpha-renamed equations compare equal.  EVar is used for both type
        -- constructors and type variables, so only v `elem` qs are renamed.
        canon qs t = subst [ (v, EVar (mkIdent ('$' : show n))) | (v, n) <- zip qs [(0 :: Int)..] ] t
        newPats = map (canon vs) pats
        newRhs = canon vs rhs
        canonEq (evks, eps, erhs) = (map (canon evks) eps, canon evks erhs)
        matchEq s (eps, _) =
          case matchFamEqn s vs newPats eps of
            MatchSubst _ -> True
            _ -> False
        isCoincident s e =
          let ce = canonEq e
          in matchEq s ce && newRhs `eqEType` snd ce
        isDuplicate s e = matchEq s (canonEq e)

-- Has this exact equation already been registered (used for idempotent
-- class-default instantiation)?
hasTypeInst :: Ident -> [EType] -> EType -> T Bool
hasTypeInst qfam pats rhs = do
  syns <- gets synTable
  case M.lookup qfam syns of
    Just old | Just (False, _, _, eqns) <- unTFamEntry old ->
      return (any (\(_, ps, r) -> length ps == length pats &&
                                  and (zipWith eqEType ps pats) && r `eqEType` rhs) eqns)
    _ -> return False

-- Do kind checking of all typeish definitions.
-- Takes the module's definitions for resolving family arities.
tcDefType :: HasCallStack => [EDef] -> EDef -> T EDef
tcDefType ds def = do
  case def of
    Data    lhs cs ds      -> withLHS lhs $ \ lhs' kr0 -> do
                                unify (getSLoc lhs) (snd (getArrows kr0)) kType
                                cm kr0         <$> (Data    lhs'  <$> mapM tcConstr cs <*> mapM (tcDeriving lhs') ds)
    Newtype lhs c  ds      -> withLHS lhs $ \ lhs' kr0 -> do
                                unify (getSLoc lhs) (snd (getArrows kr0)) kType
                                cm kr0         <$> (Newtype lhs'  <$> tcConstr c       <*> mapM (tcDeriving lhs') ds)
    Type    lhs t          -> withLHS lhs $ \ lhs' _   -> first              (Type    lhs') <$> tInferTypeT t
    Class   ctx lhs fds ms -> withLHS lhs $ \ lhs' _   -> cm kConstraint <$> (Class         <$> tcCtx ctx <*> return lhs' <*> mapM tcFD fds <*> mapM tcMethod ms)
    TypeFam lhs mk inj meqns -> withLHS lhs $ \ lhs'@(_, fvks) kr0 -> do
                                resK <- tcFamResKind kr0 mk
                                meqns' <- case meqns of
                                            Nothing -> return Nothing
                                            Just eqns -> Just <$> mapM (tcClosedEqn fvks resK) eqns
                                return (TypeFam lhs' (Just resK) inj meqns', resK)
    TypeInst vks fam pats rhs -> do
                                (vks', qfam, pats', rhs') <- checkTypeInst ds vks fam pats rhs
                                return (TypeInst vks' qfam pats' rhs')
    DataFam lhs mk         -> withLHS lhs $ \ lhs' kr0 -> do
                                resK <- tcFamResKind kr0 mk
                                return (DataFam lhs' (Just resK), resK)
    Sign      is t         ->                                            Sign      is   <$> tCheckTypeTImpl QImpl kType t
    ForImp cc ie i t       ->                                            ForImp cc ie i <$> tCheckTypeTImpl QImpl kType t
    Instance ct m e        ->                                            Instance       <$> tCheckTypeTImpl QExpl kConstraint ct <*> return m <*> return e
    Default mc ts          ->                                            Default (Just c) <$> mapM (tcDefault c) ts
                                                                           where c = fromMaybe num mc
-- We cant't do this now, because the classTable has not been fully populated yet.
-- Instead, we do it in the deriving stage.
--    StandDeriving st _ ct  ->                                            tcStand st ct
    _                      -> return def
 where
   cm = flip (,)
   tcMethod (Sign    is t) = Sign    is <$> (tCheckTypeTImpl QImpl kType t >>= expandSyn)
   tcMethod (DfltSign i t) = DfltSign i <$> (tCheckTypeTImpl QImpl kType t >>= expandSyn)
   tcMethod (TypeInst vks fam pats rhs) = do
     (vks', qfam, pats', rhs') <- checkTypeInst ds vks fam pats rhs
     return (TypeInst vks' qfam pats' rhs')
   tcMethod m              = return m
   tcFD (is, os) = (,) <$> mapM tcV is <*> mapM tcV os
     where tcV i = do { _ <- tLookup "fundep" i; return i }
   num = mkBuiltin noSLoc "Num"
   tcDefault c t = do
     EApp _ t' <- tCheckTypeT kConstraint (EApp (EVar c) t)
     return t'

-- Result kind of a type/data family declaration; inherits standalone kind
-- signature result kind via kr0 (which zonks to Type if unconstrained).
tcFamResKind :: HasCallStack => EKind -> Maybe EKind -> T EKind
tcFamResKind kr0 Nothing = return kr0
tcFamResKind kr0 (Just k) = do
  k' <- tcKind (Check sKind) k
  unify (getSLoc k) kr0 k'
  return k'

-- Replace wildcard '_' occurrences in type/data family pattern arguments
-- with fresh distinct pattern type variables before implicit-variable
-- discovery and kind checking.
freshenTypePats :: [EType] -> T [EType]
freshenTypePats = mapM go
  where
    go (EVar v) | isDummyIdent v = EVar <$> newIdent (getSLoc v) "tw"
    go (EApp f a) = EApp <$> go f <*> go a
    go (ETuple ts) = ETuple <$> mapM go ts
    go (EListish (LList ts)) = (EListish . LList) <$> mapM go ts
    go (EOper t ies) = EOper <$> go t <*> mapM (\ (i, e) -> (,) i <$> go e) ies
    go (ESign t k) = ESign <$> go t <*> pure k
    go (EParen t) = EParen <$> go t
    go (EForall b iks t) = EForall b iks <$> go t
    go t = return t

-- Kind check one closed family equation. The patterns are checked
-- against the family's parameter kinds; the rhs against the result
-- kind. All rhs variables must occur in the patterns.
tcClosedEqn :: HasCallStack => [IdKind] -> EKind -> TypeEqn -> T TypeEqn
tcClosedEqn fvks resK (eqVks, pats0, rhs) = do
  pats <- freshenTypePats pats0
  let paramKs = [ k | IdKind _ k <- fvks ]
  when (length pats /= length fvks) $
    tcError (getSLoc pats) "wrong number of patterns in closed type family equation"
  bvs <- stKeysU <$> gets valueTable
  let explicitVs = map idKindIdent eqVks
      implicitVks = [ IdKind v (EVar dummyIdent)
                    | v <- nub (freeTyVars pats)
                    , v `notElem` explicitVs
                    , v `notElem` bvs ]
  withVks (eqVks ++ implicitVks) $ \ eqVks' -> do
    pats' <- zipWithM tCheckTypeT paramKs pats
    rhs'  <- tCheckTypeT resK rhs
    let allowed = nub (bvs ++ map idKindIdent eqVks' ++ freeTyVars pats')
    mapM_ (\ v -> unless (v `elem` allowed) $
             tcError (getSLoc v) ("ambiguous type variable " ++ showIdent v ++
                                  " in closed type family equation")) (freeTyVars [rhs'])
    return (eqVks', pats', rhs')

getTypeSymTab :: T TypeTable
getTypeSymTab = do
  tcm <- gets tcMode
  case tcm of
    TCExpr -> gets typeTable
    TCType -> gets valueTable
    _      -> gets savedTypeTable

-- Resolve a (possibly unqualified) family name to its canonical
-- qualified identifier via the type table.
resolveFamId :: HasCallStack => Ident -> T Ident
resolveFamId i = do
  tt <- getTypeSymTab
  case stLookup "type" i tt of
    Right (Entry (EVar qi) _) -> return qi
    Right _ -> tcError (getSLoc i) ("not a type family: " ++ showIdent i)
    Left e -> throw e

-- Kind check a type instance equation and resolve the family name.
-- Returns the checked equation with a canonical qualified family name.
checkTypeInst :: HasCallStack => [EDef] -> [IdKind] -> Ident -> [EType] -> EType ->
                 T ([IdKind], Ident, [EType], EType)
checkTypeInst ds vks fam pats0 rhs = do
  pats <- freshenTypePats pats0
  mn <- gets moduleName
  qfam <- resolveFamId fam
  tt <- getTypeSymTab
  famKind <- case stLookup "type" qfam tt of
               Right (Entry _ k) -> return k
               Left e -> throw e
  syns <- gets synTable
  arity <- case M.lookup qfam syns >>= unTFamEntry of
    Just (_, n, _, _) -> return n
    Nothing -> case famKind of
      EUVar _ ->
        -- Family not kind-checked yet (defined later in this module):
        -- arity comes from its declaration.
        case [ length vks' | TypeFam (i, vks') _ _ _ <- ds, qualIdent mn i == qfam ] ++
             [ length vks' | DataFam (i, vks') _ <- ds, qualIdent mn i == qfam ] of
          (n:_) -> return n
          [] -> tcError (getSLoc fam) ("unknown type family: " ++ showIdent qfam)
      _ -> return (length (fst (getArrows famKind)))
  when (length pats /= arity) $
    tcError (getSLoc fam) ("wrong number of arguments in instance for " ++ showIdent qfam)
  (paramKs, resK) <- case famKind of
    EUVar _ -> (,) <$> mapM (const newUVar) pats <*> newUVar
    _ -> let (ps, r) = getArrows famKind
         in if length ps >= arity
              then let (famPs, extraPs) = splitAt arity ps
                   in return (famPs, foldr kArrow r extraPs)
              else (,) <$> mapM (const newUVar) pats <*> newUVar
  bvs <- stKeysU <$> gets valueTable
  let explicitVs = map idKindIdent vks
      implicitVks = [ IdKind v (EVar dummyIdent)
                    | v <- nub (freeTyVars pats)
                    , v `notElem` explicitVs
                    , v `notElem` bvs ]
  withVks (vks ++ implicitVks) $ \ vks' -> do
    pats' <- zipWithM tCheckTypeT paramKs pats
    rhs'  <- tCheckTypeT resK rhs
    let allowed = nub (bvs ++ map idKindIdent vks' ++ freeTyVars pats')
    mapM_ (\ v -> unless (v `elem` allowed) $
             tcError (getSLoc v) ("ambiguous type variable " ++ showIdent v ++
                                  " in instance for " ++ showIdent qfam)) (freeTyVars [rhs'])
    return (vks', qfam, pats', rhs')

-- Extract associated type/data family declarations from class heads
-- into top-level declarations, sharing the class's type variables.
-- Default type instances stay in the class for instance completion.
extractClassFams :: [EDef] -> [EDef]
extractClassFams ds = concatMap extract ds
  where extract (Class ctx lhs@(c, cvs) fds ms) =
          let (fams, rest) = partition isFamDecl ms
              isFamDecl TypeFam{} = True
              isFamDecl DataFam{} = True
              isFamDecl _ = False
              cvns = map idKindIdent cvs
              merge (TypeFam (i, vks) mk inj meqns) = TypeFam (i, mergeVks vks) mk inj meqns
              merge (DataFam (i, vks) mk) = DataFam (i, mergeVks vks) mk
              merge d = d
              mergeVks vks = cvs ++ [ vk | vk <- vks, idKindIdent vk `notElem` cvns ]
          in map merge fams ++ [Class ctx lhs fds rest]
        extract d = [d]

-- Desugar top-level data instances before kind checking.
expandTopDataInst :: EDef -> T [EDef]
expandTopDataInst d@DataInst{} = desugarDataInst d
expandTopDataInst d = return [d]

-- Desugar a data/newtype instance into a representation data/newtype
-- plus a type instance mapping the family application to it.
desugarDataInst :: EDef -> T [EDef]
desugarDataInst (DataInst isNew vks famIdent patArgs0 constrs derivs) = do
  patArgs <- freshenTypePats patArgs0
  mn <- gets moduleName
  qfam <- resolveFamId famIdent
  idx <- newUniq
  let loc = getSLoc famIdent
      dfName = unIdent (unQualIdent famIdent) ++ "$DInst$" ++ show idx
      dfIdent = mkIdentSLoc loc dfName
      fvs = nub (freeTyVars patArgs)
      kindOf v = case [ k | IdKind v' k <- vks, v' == v ] of (k:_) -> k; _ -> EVar dummyIdent
      instVks = [ IdKind v (kindOf v) | v <- fvs ]
      repTy = lhsToType (qualIdent mn dfIdent, instVks)
      famApp = eApps (EVar famIdent) patArgs
      famAppQ = eApps (EVar qfam) patArgs
      rewriteTy t | t `eqEType` famApp || t `eqEType` famAppQ = repTy
                  | otherwise =
        case t of
          EApp f a -> EApp (rewriteTy f) (rewriteTy a)
          ETuple ts -> ETuple (map rewriteTy ts)
          EListish (LList ts) -> EListish (LList (map rewriteTy ts))
          EOper t its -> EOper (rewriteTy t) (map (second rewriteTy) its)
          ESign t k -> ESign (rewriteTy t) k
          EParen t -> EParen (rewriteTy t)
          EForall b iks t -> EForall b iks (rewriteTy t)
          _ -> t
      rewriteConstr (Constr evks ctx c inf (Left sts)) =
        Constr evks (map rewriteTy ctx) c inf (Left (map (second rewriteTy) sts))
      rewriteConstr (Constr evks ctx c inf (Right fs)) =
        Constr evks (map rewriteTy ctx) c inf (Right (map (second (second rewriteTy)) fs))
      constrs' = map rewriteConstr constrs
  dataDef <- if isNew then
               case constrs' of
                 [c] -> return (Newtype (dfIdent, instVks) c derivs)
                 _ -> tcError loc "a newtype instance must have exactly one constructor"
             else return (Data (dfIdent, instVks) constrs' derivs)
  -- Seed the kind of the representation type; withLHS checks it later.
  aks <- mapM (const newUVar) instVks
  kRes <- newUVar
  extValQTop dfIdent (foldr kArrow kRes aks)
  return [dataDef, TypeInst instVks qfam patArgs repTy]
desugarDataInst d = return [d]

-- A standalone deriving has a regular instance head.
-- If it has a via clause, the via type has to have the same kind
-- as the type in the instance head.
tcStand :: DerStrategy -> EConstraint -> T EDef
tcStand st ct = do
     ct' <- tCheckTypeTImpl QExpl kConstraint ct
     -- We need the kind of the type in the instance head.
     -- It's needed for the number of arguments to "eta reduce",
     -- and also for kind checking the via type.
     -- So find the kind of the last argument to the class
     (vks, kty) <- do
       let (cvks, _ctx, cty) = splitContext ct'
           cls = fst $ getApp cty
       ctbl <- gets classTable
       case M.lookup cls ctbl of
         Just (ClassInfo vks@(_:_) _ _ _ _) -> case last vks of IdKind _ k -> return (cvks, k)
         _ -> tcError (getSLoc ct) $ "not a class " ++ showIdent cls
     let narg = length $ fst $ getArrows kty
     st' <-
       case st of
         DerVia t -> DerVia <$> withExtVals (map (\ (IdKind i k) -> (i, k)) vks)
                       (tCheckTypeT kty t)   -- make sure the via type has the same kind
         _ -> return st
     pure $ StandDeriving st' narg ct'

-- The type variables vks are already in scope when we get here.
-- With
--  tyId :: k1 -> ... -> kn -> Type
-- and
--  cls = C t1 ... tj
--  C :: (kk1 -> ... -> kkj -> kk -> Type) -> Constraint
--        ...............................  this is k below
-- then we need to find a k such that
--  cls (tyId v1 ... vk) is well kinded.
tcDeriving :: LHS -> Deriving -> T Deriving
tcDeriving (tyId, vks) (Deriving strat cs) = do
  let tcDerive (_, cls) = do
        let loc = getSLoc cls
        -- The kind of cls has to be of the form (k1 -> ... kn -> Type) -> Constraint
        -- Check that it is.
        vkk <- newUVar
        --traceM $ "tcDerive 1: " ++ show cls
        cls' <- tCheckTypeTImpl QExpl (vkk `kArrow` kConstraint) cls
        --traceM $ "tcDerive 2: " ++ show cls'
--        do { vkk' <- derefUVar vkk; traceM $ "vkk=" ++ show vkk' }
        (kks, _) <- getArrows <$> derefUVar vkk      -- arrows in kk
        -- The checking that the final kind is Type happens with the tc call below.
        let kkn = length kks                        -- number of arrows in kk
            n = length vks                          -- number of args given to the data type
            k = n - kkn
            ty = tApps tyId (map (EVar . idKindIdent) (take k vks))
--        traceM $ "tcDeriving tyId=" ++ show tyId ++ " vks=" ++ show (map idKindIdent vks) ++ " cls=" ++ show cls ++ " kkn,n,k=" ++ show (kkn,n,k) ++ " ty=" ++ show ty
        when (k < 0) $
          tcError loc "Bad deriving"
        -- The generated instance has the form 'instance ... => cls ty'.
        -- Check that this has kind Constraint.
        -- Also check that any via type also fulfills this.
        let tc t = do _ <- tCheckTypeTImpl QExpl kConstraint (tApp cls t); return ()
        tc ty
        case strat of
          DerVia via -> tc via  -- XXX should this allow implicit quantification?
          _        -> return ()
--        traceM ("tcDerive: return " ++ show (kkn, cls'))
        return (kkn, cls')


  cs' <- mapM tcDerive cs
  -- Ignore the kind here, it's checked for each derived type
  strat' <- case strat of
              DerVia t -> DerVia . fst <$> tInferTypeT t
              _        -> return strat
  return $ Deriving strat' cs'

withLHS :: forall a . HasCallStack => LHS -> (LHS -> EKind -> T (a, EKind)) -> T a
withLHS (i, vks) ta = do
  (_, ki) <- tLookupV i
  withVks vks $ \ vks0 -> do
    kr0 <- newUVar
    let kapp0 = foldr (kArrow . (\ (IdKind _ k) -> k)) kr0 vks0
    -- Pre-unify against ki so standalone kind signatures inform parameter
    -- and result kinds inside the declaration body (e.g. closed equations).
    _ <- subsCheckRho (getSLoc i) eCannotHappen ki kapp0
    vks' <- mapM (\ (IdKind v k) -> IdKind v <$> derefUVar k) vks0
    kr0' <- derefUVar kr0
    (a, kr) <- ta (i, vks') kr0'
    unify (getSLoc i) kr0' kr
    return a

tcCtx :: HasCallStack => [EConstraint] -> T [EConstraint]
tcCtx = mapM (tCheckTypeT kConstraint)

tcConstr :: HasCallStack => Constr -> T Constr
tcConstr (Constr iks ct c inf ets) =
  assertTCMode (==TCType) $
  withVks iks $ \ iks' ->
    Constr iks' <$> tcCtx ct <*> pure c <*> pure inf <*>
      case ets of
        Left  x -> Left  <$> mapM (\ (s,t)     ->        (,)s <$> tcTypeT (Check kType) t) x
        Right x -> Right <$> mapM (\ (i,(s,t)) -> (,)i . (,)s <$> tcTypeT (Check kType) t) x

-- Expand a class defintion to
--  * a "data" type for the dictionary, with kind Constraint
--  * superclass selectors
--  * method selectors
--  * default methods
-- E.g.
--   class Eq a where
--     (==) :: a -> a -> Bool
--     (/=) :: a -> a -> a
--     x /= y = not (x == y)
-- expands to
--   data Eq a = Eq$ (a -> a -> Bool) (a -> a -> Bool)
--               :: Constraint
--   == :: forall a . Eq a -> (a -> a -> Bool)
--   == (Eq x _) = x
--   /= :: forall a . Eq a -> (a -> a -> Bool)
--   /= (Eq _ x) = x
--   ==$dflt :: forall a . (Eq a) => (a -> a -> Bool)
--   ==$dflt = _noDefault "Eq.=="
--   /=$dflt :: forall a . (Eq a) => (a -> a -> Bool)
--   /=$dflt x y = not (x == y)
--
--   class (Eq a) => Ord a where
--     (<=) :: a -> a -> Bool
-- expands to
--   data Ord a = Ord$ (Eq a) (a -> a -> Bool)
--   Ord$super1 :: forall a . Ord a -> Eq a
--   <= :: forall a . Ord a -> (a -> a -> Bool)
--   <=$dflt = _noDefault "Ord.<="
--
--   instance Eq Int where (==) = primEqInt
-- expands to
--   inst$999 = Eq$ meth$1 meth$2
--     where meth$1 = primEqInt
--           meth$2 = /=$dflt dict$999
--
--   instance Ord Int where (<=) = primLEInt
-- expands to
--   inst$888 = Ord$ dict$ meth$1
--     where meth$1 = primLEInt
-- where dict$ is a special magic identifier that the type checker expands
-- to whatever dictionary is forced by the type.
-- In this case (dict$ :: Eq Int), so it with be inst$999
--
-- The actual definitions for the constructor and methods are added
-- in the desugaring pass.
-- Default methods are added as actual definitions.
-- The constructor and methods are added to the symbol table in addValueType.
expandClass :: EDef -> T [EDef]
expandClass dcls@(Class _ctx (iCls, vks) _fds ms) = do
  mn <- gets moduleName
  let
      meths = [ b | b@(Sign _ _) <- ms ]
      mdflts = [ (i, eqns) | Fcn i eqns <- ms ]
      dflttys = [ (i, t) | DfltSign i t <- ms ]
      tCtx = tApps (qualIdent mn iCls) (map (EVar . idKindIdent) vks)
      mkDflt (Sign is t) = concatMap method is
        where method methId = [ Sign [iDflt] $ EForall QExpl vks $ tCtx `tImplies` ty, def $ lookup methId mdflts ]
                where ty = fromMaybe t $ lookup methId dflttys
                      def Nothing = Fcn iDflt $ etaExp ty noDflt
                      def (Just eqns) = Fcn iDflt eqns
                      iDflt = mkDefaultMethodId methId
                      noDflt = mkExn (getSLoc methId) (unIdent methId) "noMethodError"
      mkDflt _ = impossible
      -- The type checker cannot handle something like
      --   foo :: ((forall a . a -> Int) -> Int) -> Int
      --   foo = undefined
      -- but the eta expanded version is acceptable, so we eta expand
      -- default methods.
      -- XXX This isn't really enough for complicated nested quantifiers.
      etaExp t e =
        let n = countArrows t
            vs = replicate n (EVar dummyIdent)
        in  [Eqn vs $ simpleAlts e]
      dDflts = concatMap mkDflt meths
  case map fst mdflts \\ [ i | Sign is _ <- meths, i <- is ] of  -- defaults without a signature
    i:_ -> tcError (getSLoc i) $ "missing method signature: " ++ showIdent i
    _ -> return ()
  return $ dcls : dDflts
expandClass d = return [d]

-- Ignoring initial quantifiers and context, how many arrows does the type have?
countArrows :: EType -> Int
countArrows (EForall _ _ t) = countArrows t
countArrows t | Just (_, t') <- getImplies t = countArrows t'
              | otherwise = length . fst . getArrows $ t

simpleEqn :: Expr -> [Eqn]
simpleEqn e = [Eqn [] $ simpleAlts e]

simpleAlts :: Expr -> EAlts
simpleAlts e = EAlts [([], e)] []

-- Due to the way fundeps are resolved we need to canonicalize the them.
-- If there are fundeps 'a->b, c->d' we needs to add their combination 'a c -> b d'.
-- Furthermore, we need to take the transitive closure.  So of we have 'a -> b, b -> c'
-- we need to have 'a -> b c, b -> c'.
-- This uses very slow algorithms, but given the size of fundeps that doesn't matter.
mkIFunDeps :: [Ident] -> [FunDep] -> [IFunDep]
mkIFunDeps vs afds =
  let fdss :: [[FunDep]]
      fdss = filter (not . null) $ subsequences $ closure $ map normal afds  -- all possible non-empty combinations
      fds :: [FunDep]
      fds = nub $ filter (not . null . snd) $
            map (\ xs -> let (iss, oss) = unzip xs in red (conc iss) (conc oss)) fdss
      conc :: [[Ident]] -> [Ident]
      conc = nub . sort . concat
      red :: [Ident] -> [Ident] -> ([Ident], [Ident])
      red is os = (is, os \\ is)  -- don't repeat an input in the output
      normal :: FunDep -> FunDep  -- avoid duplications and input variables among the outputs
      normal (is, os) = (is', nub os \\ is') where is' = nub is
      closure :: [FunDep] -> [FunDep]
      closure cfds =
        let cfds' = closeStep cfds
            closeStep = map addTrans
            addTrans (is, os) = (is, (xs \\ is) ++ os)
              where xs = nub $ concatMap trans cfds
                    trans (tis, tos) | null (tis \\ os) = tos \\ os  -- all inputs included in the output, so add these
                                     | otherwise = []
        in  if cfds == cfds' then cfds else closure cfds'
  in  --trace ("mkIFunDeps " ++ show (afds, fds)) $
      map (\ (is, os) -> (map (`elem` is) vs, map (`elem` os) vs)) fds

-- Turn (unqualified) class and method names into a default method name
mkDefaultMethodId :: Ident -> Ident
mkDefaultMethodId meth = addIdentSuffix meth defaultSuffix

isDefaultMethodId :: Ident -> Bool
isDefaultMethodId i = defaultSuffix `isSuffixOf` unIdent i

-- Is the second ident the default method of the first
isDefaultMethodOfId :: Ident -> Ident -> Bool
isDefaultMethodOfId i di =
  maybe False (\ s -> unIdent i == s) $
    stripSuffix defaultSuffix (unIdent di)

defaultSuffix :: String
defaultSuffix = uniqIdentSep ++ "dflt"

assocTypeSuffix :: String
assocTypeSuffix = uniqIdentSep ++ "atyp"

mkAssocTypeId :: Ident -> Ident
mkAssocTypeId fam = addIdentSuffix fam assocTypeSuffix

isAssocTypeId :: Ident -> Bool
isAssocTypeId i = assocTypeSuffix `isSuffixOf` unIdent i

unAssocTypeId :: Ident -> Maybe Ident
unAssocTypeId i = mkIdentSLoc (getSLoc i) <$> stripSuffix assocTypeSuffix (unIdent i)

isAssocTypeOfId :: Ident -> Ident -> Bool
isAssocTypeOfId i ai = maybe False (== unIdent i) (stripSuffix assocTypeSuffix (unIdent ai))

addClassTypeAssocs :: [EDef] -> T ()
addClassTypeAssocs origDs = do
  mn <- gets moduleName
  tt <- gets typeTable
  let entries =
        [ (qualIdent mn cls, [ValueExport (mkAssocTypeId fam) e])
        | Class _ (cls, _) _ ms <- origDs
        , fam <- [ i | TypeFam (i, _) _ _ _ <- ms ] ++ [ i | DataFam (i, _) _ <- ms ]
        , Right e <- [stLookup "" (qualIdent mn fam) tt]
        ]
  modify $ \ ts -> ts { assocTable = foldl' (\ m (k, v) -> M.insertWith mergeVEAssoc k v m) (assocTable ts) entries }

-- Split something of the form
--  forall vs . ctx => t
-- into (vs, ctx, t)
splitContext :: EConstraint -> ([IdKind], [EConstraint], EConstraint)
splitContext (EForall _ iks t) =
  case splitContext t of
    (iks', ctx, ct) -> (iks ++ iks', ctx, ct)
splitContext act =
  case getImplies act of
    Just (ctx, ct) ->
      case splitContext ct of
        (iks, ctxs, ct') -> (iks, ctx : ctxs, ct')
    _ -> ([], [], act)

-- Convert a Set of Classes to a list while expanding synonyms
expandTup :: EType -> T [EType]
expandTup t = do
  u <- expandSyn t
  case getExprTuple u of
    Just xs -> concat <$> mapM expandTup xs
    Nothing -> pure [u]

-- expandInst runs when all kind checking has been done, but no value checking.
-- So any generated type expressions must be kind correct and fully qualified,
-- whereas value expressions do not.
expandInst :: [EDef] -> EDef -> T [EDef]
expandInst allDs dinst@(Instance act bs extra) = do
  let (famBs, bsOk) = partition isFamInst bs
      (famExtra, extraOk) = partition isFamInst extra
      isFamInst TypeInst{} = True
      isFamInst DataInst{} = True
      isFamInst _ = False
  (vks, ctx, uccs) <- splitContext <$> expandSyn act
  ccs <- expandTup uccs
  (instBinds, defs) <- unzip <$> forM ccs (\ cc -> do
    let loc = getSLoc act
        qiCls = getAppCon cc
        iInst = mkInstId loc cc
--    tcTrace ("expandInst " ++ show iInst)
--    (e, _) <- tLookupV iCls
    ct <- gets classTable
--    let qiCls = getAppCon e

    -- Lookup known class: supers => _ | fds where mits
    (ClassInfo _ supers _ mits fds) <-
      case M.lookup qiCls ct of
        Nothing -> tcError loc $ "not a class " ++ showIdent qiCls
        Just x -> return x

    let lbs = filter ((0 /=) . instBind) bsOk
        signs = [ (i, t) | Sign is t <- lbs, i <- is ]
        addSign i e = maybe e (ESign e) $ lookup i signs
        clsMdl = qualOf qiCls                   -- get class's module name
        ies = [(i, addSign i $ ELam loc qs) | Fcn i qs <- lbs]
        meth (i, t) = fromMaybe (mkDefault i t) $ lookup i ies
        meths = map meth mits
        sups = map (const (EVar $ mkIdentSLoc loc dictPrefixDollar)) supers
        args = sups ++ meths
        lengthMaybe :: Maybe EType -> Int
        lengthMaybe Just{} = 1
        lengthMaybe Nothing = 0
        instBind (Fcn i _) = lengthMaybe $ lookup i mits
        instBind (Sign is _) = sum ((\ i -> lengthMaybe $ lookup i mits) <$> is)
        instBind _ = 0
        -- When the method type has nested quantifiers the type checker cannot handle
        --  m = mDflt
        -- so we eta expand the definition t
        --  m $1 ... = mDflt $1 ...
        mkDefault i t = ELam loc [Eqn vs $ simpleAlts $ eApps (EVar dfltId) vs]
          where dfltId = setSLocIdent loc $ mkDefaultMethodId $ qualIdent clsMdl i
                vs = [EVar $ mkIdentSLoc loc $ "$" ++ show k | k <- [0 .. countArrows t - 1] ]

    let body = eEqns [] $ eLetB extra $ eApps (EVar $ mkClassConstructor qiCls) args
        bind = Fcn iInst body
        sign = Sign [iInst] $ eForall vks $ addConstraints ctx cc
    addInstTable [(EVar iInst, vks, ctx, cc, fds)]
    return (instBind, [sign, bind])
    )

  let instBindSum = foldr (\ f b x -> f x + b x) (const 0) instBinds
  case filter ((1 /=) . instBindSum) bsOk of
    [] -> return ()
    b:_ -> tcError (getSLoc b) (if instBindSum b < 1
      then "superflous instance binding"
      else "ambiguous instance binding"
      )

{-
  if qiCls == identDataTypeableTypeable then
    trace ("instance Typeable ignored"
    return []
   else
-}
  famDefs <- processInstFams allDs vks ccs (famBs ++ famExtra)
  return (dinst : concat defs ++ famDefs)

expandInst _ d = return [d]

-- Process associated type/data instances inside an instance body:
-- kind-check and register explicit ones, desugar data instances
-- (with deriving and recursive instance expansion), and instantiate
-- class defaults for associated families the instance omits.
processInstFams :: [EDef] -> [IdKind] -> [EType] -> [EDef] -> T [EDef]
processInstFams allDs _ivks ccs famBinds = do
  mn <- gets moduleName
  let arities = [ (c, args) | cc <- ccs, let (c, args) = getApp cc ]
  explicit <- forM famBinds $ \ b -> case b of
    TypeInst vks fam pats rhs -> do
      ti'@(TypeInst vks' qfam pats' rhs') <- withTypeTable $ do
        (vks1, qfam1, pats1, rhs1) <- checkTypeInst allDs vks fam pats rhs
        zonkTypeDef (TypeInst vks1 qfam1 pats1 rhs1)
      registerTypeInst vks' qfam pats' rhs'
      return (Just qfam, [ti'])
    DataInst isNew vks fam pats constrs derivs -> do
      (_defs, checked) <- withTypeTable $ do
        ds' <- desugarDataInst (DataInst isNew vks fam pats constrs derivs)
        ch0 <- mapM (tcDefType (allDs ++ ds')) ds'
        vt <- gets valueTable
        vt' <- mapMSymTab (\ (Entry i k) -> Entry i <$> zonkKindExpr k) vt
        putValueTable vt'
        ch  <- mapM zonkTypeDef ch0
        return (ds', ch)
      mapM_ addTypeAndData checked
      derived <- concat <$> mapM doDeriving checked
      expanded <- concat <$> mapM (expandInst allDs) derived
      let qfams = [ q | TypeInst _ q _ _ <- checked ]
      return (listToMaybe qfams, checked ++ expanded)
    _ -> return (Nothing, [])
  let explicitQFams = [ q | (Just q, _) <- explicit ]
      explicitDefs = concat [ ds | (_, ds) <- explicit ]
  -- Class defaults for omitted associated families, per instance head.
  defInsts <- fmap concat $ forM arities $ \ (cls, args) -> do
    case [ (cvs, ms) | Class _ (c, cvs) _ ms <- allDs, qualIdent mn c == cls ] of
      [] -> return []  -- imported class: defaults unavailable
      ((cvs, ms) : _) -> do
        let defaults = [ d | d@TypeInst{} <- ms ]
        fmap concat $ forM defaults $ \ (TypeInst dvs dfam dpats drhs) -> do
          qdfam <- resolveFamId dfam
          if qdfam `elem` explicitQFams then return []
            else do
              let sub = zip (map idKindIdent cvs) args
                  pats' = map (subst sub) dpats
                  rhs' = subst sub drhs
              pats'' <- withTypeTable $ mapM expandSyn pats'
              rhs''  <- withTypeTable $ expandSyn rhs'
              let pvs = nub (freeTyVars pats'')
                  vks'' = map (`IdKind` kType) pvs
              dup <- hasTypeInst qdfam pats'' rhs''
              if dup then return []
                else do
                  registerTypeInst vks'' qdfam pats'' rhs''
                  return [TypeInst vks'' qdfam pats'' rhs'']
  return (explicitDefs ++ defInsts)

---------------------

recPatFields :: [IdKind] -> [Ident]
recPatFields vks = [ f | IdKind f (EVar k) <- vks, k == mkIdent "$recpat" ]

tcDefsValue :: HasCallStack => [EDef] -> T [EDef]
tcDefsValue adefs = do
--  tcTrace $ "tcDefsValue: ------------ start"
  -- Gather up all type signatures, and put them in the environment.
  -- Definitions with no type signature will be missing.
  let recPatMap = M.fromList [ (ip, fs) | Pattern (ip, vks) _ _ <- adefs, let fs = recPatFields vks, not (null fs) ]
  mapM_ (addValueType recPatMap) adefs
  defs <- concat<$> mapM (dsPatBind <=< dsEFieldsBind) adefs
  let sccs = fst $ sccDefs defs
      tcSCC (AcyclicSCC d@Pattern{}) = tcPatSyn d
      tcSCC (AcyclicSCC d) = tInferDefs [d]
      tcSCC (CyclicSCC ds) = tInferDefs ds
  --traceM $ "tcDefsValue: unsigned=" ++ show unsigned
  -- type infer and enter each SCC in the symbol table
  -- return inferred Sign
  signDefs <- mapM tcSCC sccs
  defs' <- concat <$> mapM expandPatSyn defs
--  traceM $ "tcDefsValue: ------------ expandPatSyn"
--  traceM $ showEDefs defs'
--  tcTrace $ "tcDefsValue: ------------ check"
  --  type check all definitions (the inferred ones will be rechecked)
  defs'' <- mapM (\ d -> do { tcReset; tcDefValue d}) defs'
  let defs''' = concat signDefs ++ defs''
--  traceM $ "tcDefsValue: ------------ done"
--  traceM $ showEDefs defs'''
  pure defs'''

-- Find definitions without a type signature and split them
-- into strongly connected components.
-- Also return definitions with signatures.
sccDefs :: [EDef] -> ([SCC EDef], [EDef])
sccDefs defs =
  let smap = M.fromList $ [ (i, ()) | Sign is _ <- defs, i <- is ]
      -- Split Fcn into those without and with type signatures
      (unsigns, signs) = partition noSign defs
        where noSign (Fcn i _) = hasNoSign i
              noSign (Pattern (i, _) _ _) = hasNoSign i
              noSign (PatBind _ _) = impossible
              noSign _ = False
              hasNoSign i = isNothing $ M.lookup i smap
      recFieldMap = M.fromList [ (f, i) | Pattern (i, vks) _ _ <- unsigns, f <- recPatFields vks ]
      mapRecVars = map (\ v -> fromMaybe v (M.lookup v recFieldMap))
      -- split the unsigned defs into strongly connected components
      sccs = stronglyConnComp $ map node unsigns
        where node d@(Fcn i e)               = (d, i, mapRecVars (allVarsEqns e))  -- XXX should really be allFreeVars
              node d@(Pattern (i, vks) p me) = (d, i, mapRecVars (filter (`notElem` map idKindIdent vks) (allVarsPat p (maybe [] allVarsEqns me))))
              node _ = undefined
  in  (sccs, signs)

-- Infer a type for a strongly connected component of definitions.
-- Enter the deduced types into the global symbol table and return
-- signatures with the deduced types.
tInferDefs :: [EDef] -> T [EDef]
tInferDefs fcns = do
--  traceM "tInferDefs"
  tcReset
  -- Invent type variables for the definitions
  xts <-
       let f (Fcn i _)            = do t <- newUVar; pure [(i, t)]
           f (Pattern (i, _) _ _) = do t <- newUVar; pure [(i, t)]
           f _                    = impossible
       in  concat <$> mapM f fcns
  --tcTrace $ "tInferDefs: " ++ show (map fst xts)
  -- Temporarily extend the local environment with the type variables
  withExtVals xts $ do
    -- Infer types for all the Fcns, ignore the new bodies.
    -- The bodies will be re-typecked in tcDefsValues.
    let tc (Fcn _ eqns) (_, t)   = do tcEqns False t eqns; return ()
        tc (Pattern (i,_) _ _) _ = tcError (getSLoc i) "Cannot infer recursive pattern synonym types"
        tc _ _ = impossible
    zipWithM_ tc fcns xts
  -- Get the unsolved constraints
  ctx <- getUnsolved
  -- For each definition, quantify over the free meta variables, and include
  -- context mentioning them.
  let genTop :: (Ident, EType) -> T EDef
      genTop (i, t) = do
        t' <- derefUVar t
        let vs = metaTvs [t']
            ctx' = filter (\ c -> not (null (vs `intersect` metaTvs [c]))) ctx
            t'' = addConstraints ctx' t'
            vs' = metaTvs [t'']
        t''' <- quantify vs' t''
        --tcTrace $ "tInferDefs: " ++ showIdent i ++ " :: " ++ showEType t'''
        extValQTop i t'''
        return $ Sign [i] t'''
  mapM genTop xts

getUnsolved :: T [EConstraint]
getUnsolved = do
  _ <- solveConstraints
  ctx <- gets (map snd . constraints)
  ctx' <- mapM derefUVar ctx
  putConstraints []
  return $ nubBy eqEType ctx'

addValueType :: M.Map [Ident] -> EDef -> T ()
addValueType recPatMap adef = do
  mn <- gets moduleName
  -- tcTrace ("addValueType: " ++ showEDefs [adef])
  let addConFields _     (Constr _ _ _ _ (Left _)) = return ()
      addConFields tycon (Constr evks _ _ _ (Right fs)) = mapM_ addField fs
        where evs = map idKindIdent evks
              -- Don't add fields with existentials
              addField (fld, (_, ty)) | null (freeTyVars [ty] `intersect` evs) = do
                (fe, fty) <- tLookup "addValueType?" $ mkGetName tycon fld
                extValETop fld fty fe
              addField _ = return ()

  case adef of
    Sign is@(i:_) t | isConIdent i -> do
      -- pattern signature
      t' <- canonPatSynType t
      mapM_ (\ p -> addPatSyn (fromMaybe [] (M.lookup p recPatMap)) t' p) is
    Sign is t ->
      -- regular signature
      mapM_ (\ i -> extValQTop i t) is
    Data (tycon, vks) cs _ -> do
      multCheck [ c | Constr _ _ c _ _ <- cs ]
      let
        cti = [ (qualIdent mn c, either length length ets + if null ctx then 0 else 1) | Constr _ ctx c _ ets <- cs ]
        tret = tApps (qualIdent mn tycon) (map tVarK vks)
        addCon (Constr evks ectx c _ ets) = do
          let ts = either id (map snd) ets
              cty = EForall QExpl vks $ EForall QExpl evks $ addConstraints ectx $ foldr (tArrow . snd) tret ts
              fs = either (const []) (map fst) ets
          extValETop c cty (ECon $ ConData cti (qualIdent mn c) fs)
      mapM_ addCon cs
      mapM_ (addConFields tycon) cs
    Newtype (tycon, vks) con@(Constr _ _ c _ ets) _ -> do
      let
        t = snd $ head $ either id (map snd) ets
        tret = tApps (qualIdent mn tycon) (map tVarK vks)
        fs = either (const []) (map fst) ets
      extValETop c (EForall QExpl vks $ EForall QExpl [] $ tArrow t tret) (ECon $ ConNew (qualIdent mn c) fs)
      addConFields tycon con
    ForImp _ _ i t -> extValQTop i t
    Class ctx (i, vks) fds ms -> addValueClass ctx i vks fds ms
    _ -> return ()

-- Add methods to symbol table
addValueTypeClass :: EDef -> T ()
addValueTypeClass (Class ctx (i, vks) fds ms) = addValueClass ctx i vks fds ms
addValueTypeClass _ = return ()

-- Add a pattern synonym (and any non-existential record selector types) to the symbol table.
addPatSyn :: [Ident] -> EType -> Ident -> T ()
addPatSyn fs at0 i = do
  at <- expandSyn at0
  mn <- gets moduleName
  let (vks1, ctx1, vks2, _ctx2, t) = splitPatSynType at
      (ats, tret) = getArrows t
      n = length ats
      qi = qualIdent mn i
      qip = mkPatSynMatch qi
      em = if null fs then EVar qip else ETuple (EVar qip : map EVar fs)
      mtch = (em, mkPatSynMatchType qip at)
      evs = map idKindIdent vks2
      addSel (fld, fty)
        | null (freeTyVars [fty] `intersect` evs) = do
            let selTy = eForall vks1 $ etImplies ctx1 $ tret `tArrow` fty
            extValQTop fld selTy
        | otherwise = return ()
  extValETop i at $ ECon $ ConSyn qi n mtch
  zipWithM_ (curry addSel) fs ats

-- Add mathods to the value table.
addValueClass :: [EConstraint] -> Ident -> [IdKind] -> [FunDep] -> [EBind] -> T ()
addValueClass ctx iCls vks fds ms = do
  mn <- gets moduleName
  let methIdTys = [ (i, t) | Sign is t <- ms, i <- is ]
      supTys = ctx  -- XXX should do some checking
      targs = supTys ++ map snd methIdTys
      qiCls = qualIdent mn iCls
      tret = tApps qiCls (map tVarK vks)
      cti = [ (qualIdent mn iCon, length targs) ]
      iCon = mkClassConstructor iCls
      iConTy = EForall QExpl vks $ foldr tArrow tret targs
      tvs = map (EVar . idKindIdent) vks
      methIdTys' = map (\ (i, t) -> (i, EForall QExpl vks $ tApps qiCls tvs `tImplies` t)) methIdTys
      addMethod (i, t) = extValETop i t (EVar $ qualIdent mn i)
  extValETop iCon iConTy (ECon $ ConData cti (qualIdent mn iCon) [])
  mapM_ addMethod methIdTys'
  -- Update class table, now with actual constructor type.
--  traceM $ "addValueClass " ++ show (iCls, vks)
  -- expand all type synonyms before entering the table
  info <- ClassInfo vks <$>
                    mapM expandSyn ctx <*>
                    expandSyn iConTy <*>
                    mapM (\ (i, t) -> (,) i <$> expandSyn t) methIdTys' <*>
                    return (mkIFunDeps (map idKindIdent vks) fds)
  addClassTable qiCls info

mkClassConstructor :: Ident -> Ident
mkClassConstructor i = addIdentSuffix i "$C"

tcDefValue :: HasCallStack =>
              EDef -> T EDef
tcDefValue adef =
  assertTCMode (==TCExpr) $
  case adef of
    Fcn i eqns -> do
      (_, t) <- tLookup "type signature" i
--      when (isConIdent i) $ do
--        tcTrace $ "tcDefValue: patsyn\n" ++ show i ++ " :: " ++ show t
--        tcTrace $ "tcDefValue:\n" ++ showEDefs [adef]
--      tcTrace $ "tcDefValue: ------- start " ++ showIdent i
--      tcTrace $ "tcDefValue: " ++ showIdent i ++ " :: " ++ showExpr t
--      tcTrace $ "tcDefValue: " ++ showEDefs [adef]
      teqns <- tcEqns True t eqns
--      tcTrace ("tcDefValue: after\n" ++ showEDefs [adef, Fcn i teqns])
--      cs <- gets constraints
--      tcTrace $ "tcDefValue: constraints: " ++ show cs
      checkConstraints
      mn <- gets moduleName
--      tcTrace $ "tcDefValue: " ++ showIdent i ++ " done"
      return $ Fcn (qualIdent' mn i) teqns
    ForImp cc ie i t -> do
      mn <- gets moduleName
      t' <- withNewtypeAsSyns (expandSynLoc t)
      pure $ ForImp cc ie (qualIdent' mn i) t'
    -- Check that a foreign export match the declaration type.
    -- In most cases the types will be the same, but the declaration can be overloaded
    -- so we need to ensure that it is compatible with the export definition.
    ForExp cc ms e t -> do
      ((e', t'), ds) <- solveAndDefault True $ tInferExpr (ESign e t)
      t'' <- withNewtypeAsSyns (expandSynLoc t')
      let e'' = eLetB (eBinds ds) e'
      pure $ ForExp cc (Just $ fromMaybe (showExpr e) ms) e'' t''
    Pattern{} -> impossible
    _ -> return adef

qualIdent' :: IdentModule -> Ident -> Ident
qualIdent' mn i | isInstId i = i
                | otherwise  = qualIdent mn i

-- This is only used during inference.
-- When doing type checking the actual Pattern definition will have been
-- removed by expandPatSyn.
-- The important thing here is the call to addPatSyn
tcPatSyn :: EDef -> T [EDef]
tcPatSyn (Pattern (ip, vks) p me) = do
--  traceM $ "tcPatSyn: enter " ++ show (ip, vks, p, me)
  let step [] t = tcPat (Check t) p
      step (ik:iks) t = do
        (ti, tr) <- unArrow (getSLoc ik) t
        withExtVal (idKindIdent ik) ti $ step iks tr
  pty <- newUVar   -- invent a type
  (sks, dicts, _p) <- step vks pty
  let ctx2 = map snd dicts
--  traceM $ "tcPatSyn: pat " ++ show (sks, ctx2)
  case me of Nothing -> pure (); Just e -> void $ tcEqns False pty e
  ctx1 <- getUnsolved
--  traceM $ "tcPatSyn: ctx " ++ show ctx1
  ty0 <- addConstraints ctx2 <$> derefUVar pty
  let ctx1' = deleteFirstsBy eqEType ctx1 ctx2   -- remove provided from required
      (sks', sub) = tyVarSubst sks ty0           -- turn skolems
      ty1 = subst sub ty0                        --    into rigid tyvars
  ty2 <- quantify (metaTvs [ty1]) (addConstraints ctx1' ty1)
  let (vs, ty3) = unForall ty2
      ty4 = eForall' QImpl (sks' ++ vs) ty3      -- add the skolems tyvars
  ty5 <- canonPatSynType ty4
--  traceM $ "tcPatSyn: tys " ++ show (ty0, ty1, ty2, ty3, ty4, ty5)
  addPatSyn (recPatFields vks) ty5 ip
--  traceM ("tcPatSyn: after " ++ show (ip, ty5))
  return [ Sign [ip] ty3 ]
tcPatSyn _ = impossible

-- Add implicit forall
addForall :: QForm -> EType -> T EType
addForall _ t@EForall{} = return t
addForall expl t = do
  bvs <- stKeysU <$> gets valueTable           -- bound outside
  let fvs = freeTyVars [t]                     -- free variables in t
      -- these are free, and need quantification.  eDummy indicates missing kind
      iks = map (\ i -> IdKind i eDummy) (fvs \\ bvs)
  --when (not (null iks)) $ tcTrace ("addForall: " ++ show (t, eForall iks t))
  return $ eForall' expl iks t

-- Add implicit forall and kind check, in type mode
tCheckTypeTImpl :: HasCallStack => QForm -> EType -> EType -> T EType
tCheckTypeTImpl expl tchk t = tCheckTypeT tchk =<< addForall expl t

-- Check type in type mode
tCheckTypeT :: HasCallStack => EType -> EType -> T EType
tCheckTypeT = tCheck tcTypeT

-- Infer type in type mode
tInferTypeT :: HasCallStack => EType -> T (EType, EKind)
tInferTypeT t = tInfer tcTypeT t

-- Kind check a type while already in type checking mode
tcTypeT :: HasCallStack =>
           Expected -> EType -> T EType
tcTypeT mk t = assertTCMode (==TCType) $ tcExpr mk (dsType t)

-- Kind check a type while in value checking mode
tcType :: HasCallStack =>
          Expected -> EType -> T EType
tcType mk = assertTCMode (==TCExpr) . withTypeTable . tcTypeT mk

-- Sort check a kind while already in sort checking mode
tcKindT :: HasCallStack =>
           Expected -> EKind -> T EKind
tcKindT mk t =
--  trace ("tcKindT: " ++ show (mk, t)) $
  assertTCMode (==TCKind) $ tcExpr mk (dsType t)

-- Sort check a kind while in type checking mode
tcKind :: HasCallStack =>
          Expected -> EKind -> T EKind
tcKind mk = assertTCMode (==TCType) . withTypeTable . tcKindT mk

-- When inferring the type, the resulting type will
-- be assigned to the TRef (using tSetRefType),
-- and can then be read of (using tGetRefType).
-- When checking, the expected type is simply given.
data Expected = Infer TRef | Check EType
--  deriving(Show)

{-
instance Show Expected where
  show (Infer r) = "(Infer " ++ show r ++ ")"
  show (Check t) = "(Check " ++ showExpr t ++ ")"
-}
instance Pretty Expected where
  pPrintPrec l _ (Infer r) = parens $ text "Infer" <+> pPrint0 l r
  pPrintPrec l _ (Check t) = parens $ text "Check" <+> pPrint0 l t


tInfer :: forall a b . HasCallStack =>
          (Expected -> a -> T b) -> a -> T (Typed b)
tInfer tc a = do
  ref <- newUniq
  a' <- tc (Infer ref) a
  t <- tGetRefType ref
  return (a', t)

tCheck :: forall a b . (Expected -> a -> T b) -> EType -> a -> T b
tCheck tc t = tc (Check t)

tInferExpr :: HasCallStack =>
              Expr -> T (Typed Expr)
tInferExpr = tInfer tcExpr

tCheckExpr :: HasCallStack =>
              EType -> Expr -> T Expr
tCheckExpr t e | Just (ctx, t') <- getImplies t = do
--  tcTrace $ "tCheckExpr: " ++ show (e, ctx, t')
  xt <- expandSyn t
  unless (eqEType t xt) undefined
  d <- newADictIdent (getSLoc e)
  e' <- withDict d ctx $ tCheckExprAndSolve t' e
  return $ eLam [EVar d] e'

tCheckExpr t e = tCheck tcExpr t e

tGetRefType :: HasCallStack =>
               TRef -> T EType
tGetRefType ref = do
  m <- gets uvarSubst
  case IM.lookup ref m of
    Nothing -> return (EUVar ref)
    Just t  -> return t

-- Set the type for an Infer
tSetRefType :: HasCallStack =>
               SLoc -> TRef -> EType -> T ()
tSetRefType loc ref t = do
  m <- gets uvarSubst
  case IM.lookup ref m of
    Nothing -> putUvarSubst (IM.insert ref t m)
    Just tt -> unify loc tt t

-- Get the type of an already set Expected
tGetExpType :: Expected -> T EType
tGetExpType (Check t) = return t
tGetExpType (Infer r) = tGetRefType r

tcExpr :: HasCallStack =>
          Expected -> Expr -> T Expr
tcExpr mt ae =
  case ae of
    -- Only literals are needed in the context, for "arising from the literal".
    ELit _ _ -> tcExprR mt ae
    _        -> tcExprR mt ae {-do
  tcTrace ("tcExpr enter: mt=" ++ show mt ++ " ae=" ++ showExpr ae)
  r <- tcExprR mt ae
  tcTrace ("tcExpr exit: " ++ showExpr r)
  return r -}
tcExprR :: HasCallStack =>
           Expected -> Expr -> T Expr
tcExprR mt ae =
  let { loc = getSLoc ae } in
--  trace ("tcExprR " ++ show (ae, mt)) $
  case ae of
    EVar i | isIdent dictPrefixDollar i -> do
             -- Magic variable that just becomes the dictionary
             d <- newIdent (getSLoc i) dictPrefixDollar
             case mt of
               Infer _ -> impossible
               Check t -> addConstraint d t
             return (EVar d)

           | isDummyIdent i -> do
             tcm <- gets tcMode
             case tcm of
               TCType -> do
                 u <- newUVar
                 k <- newUVar
                 instSigma loc u k mt
               _ -> tcError loc "_ cannot be used as a variable"
           | otherwise -> do
             -- Type checking an expression (or type)
             (e, t) <- tLookupV i
             -- Variables bound in patterns start out with an (EUVar ref) type,
             -- which can be instantiated to a polytype.
             -- Dereference such a ref.
             t' <-
               case t of
                 EUVar r -> fmap (fromMaybe t) (getUVar r)
                 _ -> return t
--             tcTrace $ "EVar: " ++ showIdent i ++ " :: " ++ showExpr t ++ " = " ++ showExpr t' ++ " mt=" ++ show mt
             instSigma loc e t' mt
    EQVar e t ->  -- already resolved, just instantiate
             instSigma loc e t mt

    EApp _ _ -> tcExprAp mt ae []

    EOper e ies -> tcOper e ies >>= tcExpr mt
    ELam _ qs -> tcExprLam mt loc qs
    EQLit lloc mq lit@(LStr _) ->
      -- Turn M."foo" into M.fromString ("foo" :: [Char])
      tcExpr mt $ EApp (EVar $ qualIdent mq $ mkIdentSLoc lloc "fromString") (ESign (ELit lloc lit) eStr)
        where eStr = EListish $ LList [EVar $ mkBuiltin loc "Char"]
    EQLit _ _ _ -> impossible
    ELit _ lit -> do
      tcm <- gets tcMode
      case tcm of
        TCType ->
          case lit of
            LStr _ -> instSigma loc (ELit loc lit) (tConI loc nameSymbol) mt
            LInteger _ -> instSigma loc (ELit loc lit) (tConI loc nameNat) mt
            _      -> impossible
        TCExpr -> do
          let getExpected (Infer _) = pure Nothing
              getExpected (Check t) = Just <$> derefUVar t
          case lit of
            LInteger i -> do
              mex <- getExpected mt
              case mex of
                -- Convert to Int in the compiler, that way (99::Int) will never involve fromInteger
                -- (which is not always in scope).
                Just (EVar v) | v == identInt     -> tcLit  mt loc (LInt    (fromInteger i))
                              | v == identInt64   -> tcLit  mt loc (LInt64  (fromInteger i))
                              | v == identWord    -> tcLit' mt loc (LInt    (fromInteger i)) (tConI loc nameWord)
                              | v == identWord64  -> tcLit' mt loc (LInt64  (fromInteger i)) (tConI loc nameWord64)
                              | v == identDouble  -> tcLit  mt loc (LDouble (fromInteger i))
                              | v == identFloat   -> tcLit  mt loc (LFloat  (fromInteger i))
                              | v == identInteger -> tcLit  mt loc lit
                _ -> do
                  (f, ft) <- tInferExpr (EVar (mkBuiltin loc "fromInteger"))
                  (_at, rt) <- unArrow loc ft
                  -- We don't need to check that _at is Integer, it's part of the fromInteger type.
                  instSigma loc (EApp f ae) rt mt
            LRat r -> do
              mex <- getExpected mt
              case mex of
                Just (EVar v) | v == mkIdent nameDouble -> tcLit mt loc (LDouble (fromRational r))
                              | v == mkIdent nameFloat  -> tcLit mt loc (LFloat (fromRational r))
                _ -> do
                  (f, ft) <- tInferExpr (EVar (mkBuiltin loc "fromRational"))
                  (_at, rt) <- unArrow loc ft
                  -- We don't need to check that _at is Rational, it's part of the fromRational type.
                  instSigma loc (EApp f ae) rt mt
            -- This implements OverloadedStrings.  It causes a small slowdown (2%)
            LStr s -> do
              mex <- getExpected mt
              case mex of
                Just (EApp (EVar lst) (EVar c))
                 | lst == identList && c == identChar -> tcLit mt loc lit
                Just (EVar bs)
                 | bs == identByteString -> tcLit mt loc (LBStr (BS.pack s))
                _ -> do
                  (f, ft) <- tInferExpr (EVar (mkBuiltin loc "fromString"))
                  (_at, rt) <- unArrow loc ft
                  -- We don't need to check that _at is String, it's part of the fromString type.
                  --tcTrace ("LStr " ++ show (loc, r))
                  instSigma loc (EApp f ae) rt mt
            -- Not LInteger, LRat, LStr
            _ -> tcLit mt loc lit
        _ -> impossible
    ECase a arms -> do
      -- XXX should look more like EIf
      (ea, ta) <- tInferExpr a
      tt <- tGetExpType mt
      earms <- mapM (tcArm tt ta) arms
      return (ECase ea earms)
    ELet bs a -> tcBinds bs $ \ ebs -> do { ea <- tcExpr mt a; return (ELet ebs ea) }
    ETuple es ->
      case unTuple mt of
        Just ts | length ts == length es -> do
          ees <- zipWithM tCheckExpr ts es
          return (ETuple ees)
        _ -> do
          (ees, tes) <- mapAndUnzipM tInferExpr es
          let
            n = length es
            ttup = tApps (tupleConstr loc n) tes
          munify loc mt ttup
          return (ETuple ees)
    EParen e -> tcExpr mt e
    EDo Nothing ass | Just appDo <- dsApplicativeDo loc ass -> tcExpr mt appDo
    EDo mmn ass -> do
      case ass of
        [] -> impossible
        [as] ->
          case as of
            SThen a -> tcExpr mt a
            s -> tcError (getSLoc s) "bad final do statement"
        as : ss -> do
          let mkQual name = maybe (mkBuiltin loc name) (\mn -> qualIdent mn (mkIdentSLoc loc name)) mmn
          case as of
            SBind p a -> do
              nofail <- failureFree p
              let
                sbind = mkQual ">>="
                x = eVarI loc "$b"
                patAlt = [(p, simpleAlts $ EDo mmn ss)]
                failMsg s = EApp (EVar (mkQual "fail")) (ELit loc (LStr s))
                failAlt =
                  if nofail then []
                  else [(eDummy, simpleAlts $ failMsg "bind")]
              tcExpr mt (EApp (EApp (EVar sbind) a)
                              (eLam [x] (ECase x (patAlt ++ failAlt))))
            SThen a -> do
              let sthen = mkQual ">>"
              tcExpr mt (EApp (EApp (EVar sthen) a) (EDo mmn ss))

            SLet bs ->
              tcExpr mt (ELet bs (EDo mmn ss))

            SRec xs -> tcExpr mt $ EDo mmn (dsSRec mmn (mkQual "_mfix") (mkQual "return") xs : ss)

    ESectL e i -> tcLSect e i >>= tcExpr mt
    ESectR i e -> tcRSect i e >>= tcExpr mt
    EIf e1 e2 e3 -> do
      e1' <- tCheckExpr (tBool (getSLoc e1)) e1
      case mt of
        Check t -> do
          e2' <- checkSigma e2 t
          e3' <- checkSigma e3 t
          return (EIf e1' e2' e3')
        Infer ref -> do
          (e2', t2) <- tInferExpr e2
          (e3', t3) <- tInferExpr e3
          e2'' <- subsCheck loc e2' t2 t3
          e3'' <- subsCheck loc e3' t3 t2
          tSetRefType loc ref t2
          return (EIf e1' e2'' e3'')

    -- Translate (if | a1; | a2 ...) into
    --           (case [] of _ | a1; | a2 ...)
    EMultiIf a ->
      case a of
        EAlts [([], e)] [] -> tcExpr mt e
        _                  -> tcExpr mt $ ECase (EListish (LList [])) [(EVar (mkIdent "_"), a)]

    EListish (LList es) ->
      case unList mt of
        Just t -> do
          es' <- mapM (tCheckExpr t) es
          return (EListish (LList es'))
        _ -> do
          te <- newUVar
          munify loc mt (tApp (tList loc) te)
          es' <- mapM (tCheckExpr te) es
          return (EListish (LList es'))
    EListish (LCompr eret ass) -> do
      let
        doStmts :: [EStmt] -> [EStmt] -> T ([EStmt], Typed Expr)
        doStmts rss xs =
          case xs of
            [] -> do
              r <- tInferExpr eret
              return (reverse rss, r)
            as : ss ->
              case as of
                SBind p a -> do
                  v <- newUVar
                  ea <- tCheckExprAndSolve (tApp (tList loc) v) a
                  tCheckPatC v p $ \ ep -> doStmts (SBind ep ea : rss) ss
                SThen a -> do
                  ea <- tCheckExprAndSolve (tBool (getSLoc a)) a
                  doStmts (SThen ea : rss) ss
                SLet bs ->
                  tcBinds bs $ \ ebs ->
                    doStmts (SLet ebs : rss) ss
                SRec _ ->
                  tcError (getSLoc as) "rec not allowed"
      (rss, (ea, ta)) <- doStmts [] ass
      let
        tr = tApp (tList loc) ta
      munify loc mt tr
      return (EListish (LCompr ea rss))
    EListish (LFrom       e)        -> tcExpr mt (enumCall loc "From" [e])
    EListish (LFromTo     e1 e2)    -> tcExpr mt (enumCall loc "FromTo" [e1, e2])
    EListish (LFromThen   e1 e2)    -> tcExpr mt (enumCall loc "FromThen" [e1,e2])
    EListish (LFromThenTo e1 e2 e3) -> tcExpr mt (enumCall loc "FromThenTo" [e1,e2,e3])
    ESign e t -> do
{-
      -- As a hack, translate 'e :: T' to 'let s$999 :: T; s$999 = e in s$999'
      -- This will ensure that dictinaries are inserted in the right place.
      i <- newIdent (getSLoc e) "s"
      tcExpr mt $ ELet [Sign [i] t, Fcn i $ eEqns [] e] (EVar i)
-}
      -- XXX wrong for kind signatures
      t' <- withTypeTable $ tCheckTypeTImpl QImpl kType t >>= expandSyn
      case splitContext t' of
        -- No context, handle this without a 'let' to avoid bloat.
        ([], [], _) -> do
          e' <- instSigma loc e t' mt
          tCheckExpr t' e'
        _ -> do
          -- We have a forall/context.  As a hack, translate 'e :: T' to
          -- let s$999 :: T; s$999 = e in s$999
          -- This will ensure that dictinaries are inserted in the right place.
          -- XXX Maybe it would be better to have this as part of the code above?
          -- Or maybe do this rewrite all the time?
          i <- newIdent (getSLoc e) "s"
          let et = ELet [Sign [i] t, Fcn i $ eEqns [] e] (EVar i)
          tcExpr mt et

    -- Only happens in type&kind checking mode.
    EForall b vks t ->
--      assertTCMode (==TCType) $
      withVks vks $ \ vks' -> do
        tt <- tcExpr mt t
        derefUVar (EForall b vks' tt)
    EUpdate e flds -> do
      ises <- concat <$> mapM (dsEField flds e) flds
      mc <- getExprCon e
      case mc of
        Nothing -> do
          let ies = [ (i, e') | EField [i] e' <- ises ]
          if length ies == length ises then do   -- all updates are non-nested
            useCase <- needDsCase mt (map fst ies) e
            -- traceM ("useCase " ++ show (ae, useCase))
            case useCase of
              Nothing -> tcExpr mt $ foldr eSetFields e ises
              Just cs -> tcExpr mt $ dsUpdateCase cs e ies
           else
            tcExpr mt $ foldr eSetFields e ises
        Just c  -> tcExpr mt =<< dsRecCon unsetField c e ises

    ESelect is -> do
        let x = eVarI loc "$x"
        tcExpr mt $ eLam [x] $ foldl (\ e i -> EApp (eGetField i) e) x is
    ETypeArg _ ->
        tcError loc "Bad type application"
    _ -> error $ "tcExpr: cannot handle: " ++ prettyShow (getSLoc ae) ++ " " ++ showExpr ae
      -- impossible

-- We need to use a case expression to do record updated if
--  * any field has existential type
--  * any field has universal type
--  * the type is polymorphic (i.e., potentially a polymorphic update)
-- This is partly guesswork.  We try:
--  * expected type known and "bad"
--  * type of scrutinee is "bad"
--  * the updated labels are not unique and all construct a "bad" type
needDsCase :: Expected -> [Ident] -> Expr -> T (Maybe [Constr])
needDsCase ex lbls ae =
  case ex of
    Infer _ -> need ae
    Check t -> liftA2 (<|>) (needT t) (need ae)
  where
    need :: Expr -> T (Maybe [Constr])
    need e = liftA2 (<|>)
               ((needT . snd) =<< noEffect (tInferExpr e))   -- try figuring out the type
               (asum <$> mapM needL lbls)
    -- Does the type need a case ?
    needT :: EType -> T (Maybe [Constr])
    needT at = do
      t <- derefUVar at >>= expandSyn
      case getAppM t of
        Nothing -> return Nothing
        Just (i, ts) -> do
          dt <- gets dataTable
          case M.lookup i dt of
            Just (Data _ cs _)   -> return $ if not (null ts) || any needC cs then Just cs  else Nothing
            Just (Newtype _ c _) -> return $ if not (null ts) ||     needC c  then Just [c] else Nothing
            _ -> return Nothing        -- we don't know which type it is
    -- Does a constructor need a case?
    -- Large records (> 32 fields, see largeRecordFieldLimit in Deriving)
    -- always use case desugaring for updates, since no SetField
    -- instance is generated for them.
    needC :: Constr -> Bool
    needC (Constr _ _ _ _ (Left _)) = False
    needC (Constr vs _ _ _ (Right fs)) = not (null vs) || length fs > 32 || any (isForall . snd . snd) fs
      where isForall (EForall _ _ _) = True
            isForall _ = False
    needL :: Ident -> T (Maybe [Constr])
    needL lbl = do
      vt <- gets valueTable
      case stLookupGlbUnqMany lbl vt of
        -- check the return type of an unambiguous label
        Just [Entry _ t] | (t':_, _) <- getArrows (dropForallContext t) -> needT t'
        _ -> return Nothing

-- Do a record update using case.
dsUpdateCase :: [Constr] -> Expr -> [(Ident, Expr)] -> Expr
dsUpdateCase cs e ies = chkUsed $ ECase e arms
  where
    loc = getSLoc e
    undef = mkExn loc "record update" "recSelError"
    hasAll fs = all ((`elem` map fst fs) . fst) ies
    matchingArms =
      [ (eApps (EVar c) xs, oneAlt $ eApps (EVar c) (zipWith fld xs fs))
      | Constr _ _ c _ (Right fs) <- cs
      , hasAll fs
      , let xs = [ EVar $ mkIdentSLoc loc $ "x$" ++ show i | i <- [1..length fs] ]
            fld x (i, _) = fromMaybe x $ lookup i ies
      ]
    arms
      | length matchingArms == length cs = matchingArms
      | otherwise                        = matchingArms ++ [(eDummy, oneAlt undef)]
    chkUsed a = case map fst ies \\ [ f | Constr _ _ _ _ (Right fs) <- cs, (f, _) <- fs ] of
                  [] -> a
                  f:_ -> errorMessage loc $ "Unknown field " ++ show f

dsSRec :: Maybe Ident -> Ident -> Ident -> [EStmt] -> EStmt
dsSRec mmn imfix iret ss =
  let vs = eTuple $ map EVar $ concatMap getStmtBound ss
  in  SBind vs $ eAppI imfix $ eLam [ELazy True vs] $ EDo mmn (ss ++ [SThen $ eAppI iret vs])

-- Desugar an ApplicativeDo-compatible 'do' block (ending in @pure body@ where
-- none of the '<-'-bound variables appear in the statement actions or let-bindings)
-- into @let ... in fmap (\x1 ... xn -> body) e1 <*> ... <*> en@.
dsApplicativeDo :: SLoc -> [EStmt] -> Maybe Expr
dsApplicativeDo loc ass
  | length ass >= 2
  , SThen lastExpr <- last ass
  , Just body <- unPure lastExpr
  , Just steps <- mapM toStep (init ass)
  , let lets = [ bs | Left bs <- steps ]
        binds = [ xe | Right xe <- steps ]
        boundVars = [ x | (x, _) <- binds, not (isDummyIdent x) ]
        rhsVars = concatMap (allVarsExpr . snd) binds ++ concatMap (concatMap allVarsBind) lets
  , ((_, e1) : rest) <- binds
  , all (`notElem` rhsVars) boundVars =
      let lam = eLam [ EVar x | (x, _) <- binds ] body
          app0 = EApp (EApp (EVar (mkBuiltin loc "fmap")) lam) e1
          appAll = foldl (\acc (_, ei) -> EApp (EApp (EVar (mkBuiltin loc "<*>")) acc) ei) app0 rest
      in Just (foldr ELet appAll lets)
  | otherwise = Nothing
  where
    unPure (EApp (EVar p) b) | unIdent (unQualIdent p) == "pure" = Just b
    unPure (EOper (EVar p) [(op, b)]) | unIdent (unQualIdent p) == "pure", unIdent (unQualIdent op) == "$" = Just b
    unPure _ = Nothing
    toStep (SBind (EVar x) e) | not (isConIdent x) = Just (Right (x, e))
    toStep (SThen e) = Just (Right (dummyIdent, e))
    toStep (SLet bs) = Just (Left bs)
    toStep _ = Nothing

-- XXX Maybe allow singleton tuples
eTuple :: [Expr] -> Expr
eTuple [e] = e
eTuple es = ETuple es

-- A heuristic to decide if an identifier is a record label.
-- If the name is in the symbol table and has function type, we say no.
isLabel :: Ident -> T Bool
isLabel i = do
  env <- gets valueTable
  case stLookup "" i env of
    Left _ -> return True  --
    Right (Entry e t) ->
      return $ isGetExpr e || countArrows t == 0

isGetExpr :: Expr -> Bool
isGetExpr (EVar g) = (getPrefix ++ ".") `isInfixOf` unIdent g
isGetExpr _ = False

tcExprAp :: HasCallStack =>
            Expected -> Expr -> [Expr] -> T Expr
--tcExprAp _ ae args | trace ("tcExprAp: " ++ show (ae, args)) False = undefined
tcExprAp mt ae args = do
  let rest = do
        (f, t) <- tInferExpr ae
        tcExprApFn mt f t args
  case ae of
    EApp f a -> tcExprAp mt f (a : args)
    EParen f -> tcExprAp mt f args
    EOper e ies -> tcOper e ies >>= \ eop -> tcExprAp mt eop args
    EVar i | isIdent dictPrefixDollar i -> impossiblePP ae
           | isDummyIdent i -> impossiblePP ae
           | otherwise -> do
             -- Type checking an expression (or type)
             (fn, t) <- tLookupV i
--             traceM ("tcExprAp " ++ show (fn, t))
             -- Variables bound in patterns start out with an (EUVar ref) type,
             -- which can be instantiated to a polytype.
             -- Dereference such a ref.
             t' <-
               case t of
                 EUVar r -> fmap (fromMaybe t) (getUVar r)
                 _ -> return t
--             tcTrace $ "exExprAp: EVar " ++ showIdent i ++ " :: " ++ showExpr t ++ " = " ++ showExpr t' ++ " mt=" ++ show mt
             case fn of
               EVar ii | ii == mkIdent "Data.Function.$", f:as <- args -> tcExprAp mt f as
               _ -> tcExprApFn mt fn t' args
    EQVar f t ->  -- already resolved
      tcExprApFn mt f t args

    ESelect is@(lbl:_) | (e:args') <- args -> do
      -- If we have parsed a e.lbl as a record select,
      -- but it turns out that the lbl is not a label,
      -- then we rejig the expression into function compositions,
      -- i.e., e . lbl.
      -- This is dodgy, since it will already have been parsed with
      -- the wrong fixity.
      b <- isLabel lbl
      if b then
        rest
       else
        let eoper = EOper e $ map (\ i -> (mkIdentSLoc (getSLoc i) ".", EVar i)) is
        in  --trace ("convert " ++ show (EApp ae e) ++ " to " ++ show eoper) $
            tcExprAp mt eoper args'

    _ -> rest

data AnArg = ArgExpr Expr EType | ArgCtx EConstraint
--  deriving Show

-- Instantiate a function, but delay generating the dictionaries.
-- When generating the dictionaries here (like tInst) there
-- is no type information; just a type variable.
-- By delaying the dictionary generation we gain more
-- type information, and can avoid let binding dictionaries by
--  * finding an already bound dictionary for the same constraint
--  * solving the constraint early
tcExprApFn :: HasCallStack =>
              Expected -> Expr -> EType -> [Expr] -> T Expr
--tcExprApFn mt fn fnt args | trace ("tcExprApFn: fn=" ++ show fn ++ ", fnt=" ++ show fnt ++ ", args=" ++ show args ++ ", mt=" ++ show mt) False = undefined
tcExprApFn mt fn atfn aargs = do
--  traceM $ "tcExprApFn: " ++ show (getSLoc aargs, mt, fn, atfn, aargs)
--  xx <- gets ctxTables
--  traceM $ "tcExprApFn: ctxTables=" ++ show xx
  let loc = getSLoc fn
--  (ctxs, tfn') <- tInstDelay atfn
--  traceM $ "tcExprApFn: (fn', tfn') = " ++ show (fn', tfn')
  let -- loop _ats aas ft | trace ("loop: " ++ show (aas, ft)) False = undefined
      loop ats [] ft = final (reverse ats) ft
      loop ats aas@(a:as) aft = do
        case nextArg aft of
          AReqd (IdKind i k) ft -> useType i k a ft
          AForall _ (IdKind i k:iks) ft | ETypeArg t <- a -> do
            -- traceM ("AForall " ++ show (i, t))
            useType i k t (EForall QExpl iks ft)
          AForall _ iks ft -> do
            ft' <- tInstForall iks ft
            loop ats aas ft'
          AConstaint ctx ft ->
            loop (ArgCtx ctx : ats) aas ft
          ARet aft' -> do
            (at, rt) <- unArrow loc aft'
            --traceM ("ARet " ++ show (at, rt))
            loop (ArgExpr a at : ats) as rt
        where useType i k t ft = do
                t' <- if t `eqEType` EVar dummyIdent
                      then newUVar
                      else tcType (Check k) t >>= expandSyn
                -- traceM ("useType: " ++ show (i, t', (subst [(i, t')] ft)))
                loop ats as (subst [(i, t')] ft)

      final :: [AnArg] -> EType -> T Expr
      final aats rt = do
{-
        rt' <- derefUVar rt
        mt' <- case mt of Check ttt -> Check <$> derefUVar ttt
                          _ -> return mt
        traceM $ "final: " ++ show (loc, aats, rt', mt')
-}
        -- We want to do the unification of rt ant mt before checking the argument to
        -- have more type information.  See tests/Eq1.hs.
        -- But instSigma may transform the input expression, so we have to be careful.
        let etmp = EUVar ugly
            ugly = -1::Int
        etmp' <- instSigma loc etmp rt mt

        let arg (ArgExpr e t) = do
--              t' <- derefUVar t
--              traceM ("final: checkSigma: " ++ show (e, t'))
              checkSigma e t
            arg (ArgCtx ctx) = newDict loc ctx
        args <- mapM arg aats
        let res = foldl EApp fn args
--        traceM (show res)

--        cc <- gets constraints
--        traceM $ "tcExprApFn: constraints=" ++ show cc

        case etmp' of
          EUVar _ -> return res   -- instSigma did nothing, this is the common case
          _ -> return $ substEUVar [(ugly, res)] etmp'


  loop [] aargs atfn

-- Is a pattern failure free?
failureFree :: EPat -> T Bool
failureFree p@(EVar _) = failureFreeAp [] p
failureFree p@(EApp _ _) = failureFreeAp [] p
failureFree (ETuple ps) = and <$> mapM failureFree ps
failureFree (ESign p _) = failureFree p
failureFree (EAt _ p) = failureFree p
failureFree (ELazy True _) = return True
failureFree (ELazy False p) = failureFree p
failureFree (EViewPat _ p) = failureFree p
failureFree (EParen p) = failureFree p
failureFree (EUpdate c fs) = do          -- record pattern, e.g. C { f = p, .. }
  b <- failureFreeAp [] c
  bs <- mapM fieldFree fs
  return (b && and bs)
  where fieldFree (EField _ p) = failureFree p
        fieldFree (EFieldPun _) = return True
        fieldFree EFieldWild = return True
failureFree _ = return False

failureFreeAp :: [Bool] -> EPat -> T Bool
failureFreeAp bs (EApp f a) = do
  b <- failureFree a
  failureFreeAp (b:bs) f
failureFreeAp bs (EVar v) | not (isConIdent v) = return True
                          | otherwise = do
                              (con, _) <- tLookupV v
                              return $ case con of
                                ECon (ConNew _ _) -> and bs
                                ECon (ConData [_] _ _) -> and bs  -- single constructor
                                _ -> False
failureFreeAp bs (ESign p _) = failureFreeAp bs p
failureFreeAp _ _ = return False  -- bad pattern, just ignore

eSetFields :: EField -> Expr -> Expr
eSetFields (EField is e) r =
  let loc = getSLoc is
      eCompose = EVar $ mkBuiltin loc "composeSet"
      has = map eHasField $ init is
      set1 = eSetField (last is)
      set = foldr (EApp . EApp eCompose) set1 has
  in  EApp (EApp set r) e
eSetFields _ _ = impossible

eHasField :: Ident -> Expr
eHasField i = EApp (EVar ihas) (eProxy i)
  where ihas = mkBuiltin (getSLoc i) "hasField"

eSetField :: Ident -> Expr
eSetField i = EApp (EVar iset) (eProxy i)
  where iset = mkBuiltin (getSLoc i) "setField"

eGetField :: Ident -> Expr
eGetField i = EApp (EVar iget) (eProxy i)
  where iget = mkBuiltin (getSLoc i) "getField"

eProxy :: Ident -> Expr
eProxy i = ESign proxy (EApp proxy (ELit loc (LStr (unIdent i))))
  where proxy = EVar $ mkBuiltin loc "Proxy"
        loc = getSLoc i

-- Turn
--   p = e
-- into (x1..xn are the variables in p)
--   tmp = e
--   x1 = case tmp of p -> x1
--   ...
--   xn = case tmp of p -> xn
-- Take care with bindings like x@p = e and turn them into
--   x = e
--   x1 = case x of p -> x1
--   ...
-- Extra weird, x@y@p
--   x = y
--   y = e
--   ...
dsPatBind :: EBind -> T [EBind]
dsPatBind (PatBind p e) = do
  let (xs, p') = getAts p
  (v, ys) <- case xs of
               [] -> do v <- newIdent (getSLoc e) patBindPrefix; return (v, [])
               v:vs -> return (v, vs)
  let de = fcn v e
      dy = map (\ y -> fcn y (EVar v)) ys
      ds = [ fcn i (ECase (EVar v) [(p', oneAlt $ EVar i)]) | i <- patVars p' ]
      fcn i b = Fcn i (eEqns [] b)
  return $ de : dy ++ ds
dsPatBind b = return [b]

patBindPrefix :: String
patBindPrefix = "pb"

isPatBindVar :: Ident -> Bool
isPatBindVar = isPrefixOf (patBindPrefix ++ uniqIdentSep) . unIdent

getAts :: EPat -> ([Ident], EPat)
getAts (EAt x p) = (x:xs, p') where (xs, p') = getAts p
getAts p = ([], p)

dsEFieldsBind :: EBind -> T EBind
dsEFieldsBind (PatBind p e) = PatBind <$> dsEFields p <*> return e
dsEFieldsBind (Pattern lhs p me) = Pattern lhs <$> dsEFields p <*> return me
dsEFieldsBind b = return b

dsEField :: [EField] -> Expr -> EField -> T [EField]
dsEField _ _ e@(EField _ _) = return [e]
dsEField _ _ (EFieldPun is) = return [EField is $ EVar (last is)]
dsEField flds e EFieldWild = do
  let loc = getSLoc e
      ids = concatMap f flds  -- fields already present
            where f (EField [i] _) = [i]
                  f (EFieldPun [i]) = [i]
                  f _ = []
  mc <- getExprCon e
  case mc of
    Just c -> return [ EField [f'] (EVar f') | f <- conFields c, f `notElem` ids, let f' = setSLocIdent loc f ]
    _ -> tcError (getSLoc e) "record wildcard not allowed"

-- Patterns need to expand EFieldWild before type checking
dsEFields :: EPat -> T EPat
dsEFields apat =
  case apat of
    EVar _ -> return apat
    EApp p1 p2 -> EApp <$> dsEFields p1 <*> dsEFields p2
    EOper p1 ips -> EOper <$> dsEFields p1 <*> mapM (\ (i, p2) -> (,) i <$> dsEFields p2) ips
    ELit _ _ -> return apat
    ETuple ps -> ETuple <$> mapM dsEFields ps
    EListish (LList ps) -> EListish . LList <$> mapM dsEFields ps
    ESign p t -> ESign <$> dsEFields p <*> pure t
    EAt i p -> EAt i <$> dsEFields p
    EViewPat e p -> EViewPat e <$> dsEFields p
    ELazy z p -> ELazy z <$> dsEFields p
    ECon _ -> return apat
    EUpdate c fs -> do
      fs' <- concat <$> mapM (dsEField fs c) fs
      EUpdate c <$> mapM (\ f -> case f of EField is p -> EField is <$> dsEFields p; _ -> impossible) fs'
    EParen p -> dsEFields p
    ENegApp _ -> return apat
    EOr ps -> EOr <$> mapM dsEFields ps
    _ -> error $ "dsEFields " ++ showExpr apat

unsetField :: Ident -> Expr
unsetField i = mkExn (getSLoc i) (unIdent i) "recConError"

-- Record construction, turn named fields into positional
dsRecCon :: (Ident -> Expr) -> Con -> Expr -> [EField] -> T Expr
dsRecCon unset c e flds = do
  let ises = map unEField flds
      fs = conFields c
      ies = map (first head) ises
      is = map fst ies
      as = map field fs
      field i = fromMaybe (unset i) $ lookup i ies
  case filter ((> 1) . length . fst) ises of
    (i:_, _):_ -> tcError (getSLoc i) "Nested fields not allowed"
    _ -> return ()
  case is \\ fs of
    vs@(v:_) -> tcError (getSLoc v) $ "extra field(s) " ++ unwords (map unIdent vs)
    _ -> return ()
  return $ eApps e as

-- Get the possible ECon from e.
getExprCon :: Expr -> T (Maybe Con)
getExprCon (EVar i) = do
  (e', _) <- tLookupV i
  case e' of
    ECon c -> return (Just c)
    _      -> return Nothing
getExprCon _ = return Nothing

enumCall :: SLoc -> String -> [Expr] -> Expr
enumCall loc f = eApps (EVar (mkBuiltin loc ("enum" ++ f)))

tcLit :: HasCallStack => Expected -> SLoc -> Lit -> T Expr
tcLit mt loc l@(LPrim _) = newUVar >>= tcLit' mt loc l
tcLit mt loc l@(LExn  _) = newUVar >>= tcLit' mt loc l
tcLit mt loc l = do
  let t =
        case l of
          LInt _     -> tConI loc nameInt
          LInt64 _   -> tConI loc nameInt64
          LInteger _ -> tConI loc nameInteger
          LDouble _  -> tConI loc nameDouble
          LFloat _   -> tConI loc nameFloat
          LChar _    -> tConI loc nameChar
          LStr _     -> tApp (tList loc) (tConI loc nameChar)
          LBStr _    -> tConI loc nameByteString
          _          -> impossible
  tcLit' mt loc l t

tcLit' :: Expected -> SLoc -> Lit -> EType -> T Expr
tcLit' mt loc l t = instSigma loc (ELit loc l) t mt

-- tcOper is in T because it has to look up identifiers, and get the fixity table.
-- But there is no type checking happening here.
tcOper :: HasCallStack =>
          Expr -> [(Ident, Expr)] -> T Expr
tcOper ae aies = do
  fixs <- gets fixTable
  let
    opfix :: (Ident, Expr) -> T ((Expr, Fixity), Expr)
    opfix (i, e) | Just 2 <- getTupleConstr i =  -- tcLSect/tcRSect can introduce ',' as an operator
      return ((EVar i, (AssocNone, -1)), e)
    opfix (i, e) = do
      (ei, _) <- tLookupV i
      let fx = getFixity fixs (getAppCon ei)
      return ((EVar i, fx), e)

  ites <- mapM opfix aies
  case resolveFixity ae ites of
    Left (loc, err) -> tcError loc err
    Right e -> return e

tcLSect :: Expr -> Ident -> T Expr
tcLSect (EOper e ies) op = do
  let x = eVarI loc "$x"
      loc = getSLoc op
  e' <- tcOper e (ies ++ [(op, x)])
  case e' of
    EApp f x' | x' `eqExpr` x -> return f
    _                         -> badSectionFixity loc
tcLSect e op | greedyExpr e = badSectionFixity (getSLoc op)
             | otherwise    = return (EApp (EVar op) e)

-- These construct have a greedy parser and cannot be in a left section
greedyExpr :: Expr -> Bool
greedyExpr (ELam _ _) = True
greedyExpr (ECase _ _) = True
greedyExpr (ELet _ _) = True
greedyExpr (EIf _ _ _) = True
greedyExpr (EDo _ _) = True
greedyExpr _ = False

tcRSect :: Ident -> Expr -> T Expr
tcRSect op (EOper e ies) = do
  let x = eVarI loc "$x"
      loc = getSLoc op
  e' <- tcOper x ((op, e):ies)
  case e' of
    EApp (EApp _ x') _ | x `eqExpr` x' -> return (eLam [x] e')
    _                                  -> badSectionFixity loc
tcRSect op e = do
  let x = eVarI (getSLoc op) "$x"
  return (eLam [x] (EApp (EApp (EVar op) x) e))

badSectionFixity :: SLoc -> T a
badSectionFixity loc = tcError loc "Bad section fixity"

unArrow :: HasCallStack =>
           SLoc -> EType -> T (EType, EType)
--unArrow _ t | trace ("unArrow: " ++ show t) False = undefined
unArrow loc (EForall _ iks t) = do
  -- Found forall in a co-variant position.
  -- Make new unique tyvars in case of clashes.
  -- XXX Is this correct?
  (_, t') <- shallowSkolemise iks t
  unArrow loc t'
unArrow loc t = do
  case getArrow t of
    Just ar -> return ar
    Nothing -> do
      a <- newUVar
      r <- newUVar
      unify loc t (tArrow a r)
      return (a, r)

unTuple :: Expected -> Maybe [EType]
unTuple (Infer _) = Nothing
unTuple (Check t) = getExprTuple t

unList :: Expected -> Maybe EType
unList (Check (EApp (EVar i) t)) | i == identList = Just t
unList _ = Nothing

getFixity :: FixTable -> Ident -> Fixity
getFixity fixs i = fromMaybe defaultFixity $ M.lookup i fixs

newADictIdent :: SLoc -> T Ident
newADictIdent loc = newIdent loc adictPrefix

newDictIdent :: SLoc -> T Ident
newDictIdent loc = newIdent loc dictPrefix

data Arg
  = AReqd         IdKind      EType       -- forall ->
  | AForall QForm [IdKind]    EType       -- forall .
  | AConstaint    EConstraint EType       -- =>
  | ARet                      EType       -- none of the above
--  deriving Show

nextArg :: EType -> Arg
nextArg (EForall _ []  t)                  = nextArg t
nextArg (EForall QReqd (ik:iks) t)         = AReqd ik (EForall QReqd iks t)
nextArg (EForall q     iks      t)         = AForall q iks t
nextArg t | Just (ctx, t') <- getImplies t = AConstaint ctx t'
          | otherwise                      = ARet t

tcExprLam :: HasCallStack => Expected -> SLoc -> [Eqn] -> T Expr
tcExprLam mt loc qs = do
  t <- tGetExpType mt
  ELam loc <$> tcEqns False t qs

tcEqns :: HasCallStack => Bool -> EType -> [Eqn] -> T [Eqn]
tcEqns top t eqns = tcEqns' top t eqns

tcEqns' :: HasCallStack => Bool -> EType -> [Eqn] -> T [Eqn]
tcEqns' top at eqns =
  case at of
    EForall QExpl iks t -> withExtTyps iks $ tcEqns' top t eqns
    EForall QImpl   _ t ->                   tcEqns' top t eqns
    _ | Just (ctx, t') <- getImplies at -> do
      let loc = getSLoc eqns
      d <- newADictIdent loc
      f <- newIdent loc "fcnD"
      withDict d ctx $ do
        eqns' <- tcEqns' top t' eqns
        let eqn =
              case eqns' of
                [Eqn [] alts] -> Eqn [EVar d] alts
                _             -> Eqn [EVar d] $ EAlts [([], EVar f)] [Fcn f eqns']
        return [eqn]
    _ -> do
      let loc = getSLoc eqns
      f <- newIdent loc "fcnS"
      (eqns', ds) <- solveAndDefault top $ mapM (tcEqn at) eqns
--  tcTrace $ "tcEqns done: " ++ showEBind (Fcn dummyIdent eqns')
      case ds of
        [] -> return eqns'
        _  -> do
          let
            bs = eBinds ds
            eqn = Eqn [] $ EAlts [([], EVar f)] (bs ++ [Fcn f eqns'])
          return [eqn]

tcEqn :: HasCallStack => EType -> Eqn -> T Eqn
--tcEqn t eqn | trace ("tcEqn: " ++ show eqn ++ " :: " ++ show t) False = undefined
tcEqn t (Eqn ps alts) =
  tcPats t ps $ \ t' ps' -> do
--      tcTrace $ "tcEqn " ++ show ps ++ " ---> " ++ show ps'
    alts' <- tcAlts t' alts
    return (Eqn ps' alts')

-- Only used above
tcPats :: HasCallStack =>
          EType -> [EPat] -> (EType -> [EPat] -> T Eqn) -> T Eqn
--tcPats t [] ta = ta t []
tcPats at pps ta =
  case nextArg at of
--    aa | trace ("tcPats: " ++ show (at, pps, aa)) False -> undefined
    AForall QExpl iks t  -> withExtTyps iks $ tcPats t pps ta
    AForall _     _    _ -> impossible   -- no nested implicit foralls
    AReqd (IdKind a k) t ->
      case pps of
        EVar i : ps -> withExtTyps [IdKind i k] $ do
          unless (isDummyIdent i) $
            addEqDict (EVar a) (EVar i)     -- This bound type variable is actually equal to the one in the signature
          tcPats t ps ta
        _ -> tcError (getSLoc pps) "Bad required type argument"
    AConstaint ctx t -> do
      d <- newADictIdent (getSLoc pps)
      withDict d ctx $ do -- XXX should we solve here?
        (eqn, ds) <- solveLocalConstraints $ tcPats t pps $ \ t' ps' -> ta t' (EVar d : ps')
        case ds of
          [] -> return eqn
          _  -> return $ addSolved ds eqn
    ARet at' ->
      case pps of
        p:ps -> do
          (tp, tr) <- unArrow (getSLoc p) at'
          -- tCheckPatC dicts used in tcAlt solve
          tCheckPatC tp p $ \ p' -> tcPats tr ps $ \ t' ps' -> ta t' (p' : ps')
        [] -> ta at' []   -- base case, no more arguments, explicit or implicit


tcAlts :: HasCallStack => EType -> EAlts -> T EAlts
tcAlts t (EAlts alts bs) =
--  trace ("tcAlts: bs in " ++ showEBinds bs) $
  tcBinds bs $ \ bs' -> do
--    tcTrace ("tcAlts: bs out " ++ showEBinds bbs)
    alts' <- mapM (tcAlt t) alts
    return (EAlts alts' bs')

tcAlt :: HasCallStack => EType -> EAlt -> T EAlt
--tcAlt t (_, rhs) | trace ("tcAlt: " ++ showExpr rhs ++ " :: " ++ showEType t) False = undefined
tcAlt t (ss, rhs) = tcGuards ss $ \ ss' -> do
  rhs' <- tCheckExprAndSolve t rhs
  return (ss', rhs')

tcGuards :: [EStmt] -> ([EStmt] -> T EAlt) -> T EAlt
tcGuards [] ta = ta []
tcGuards (SBind p e : ss) ta = do
  ((e', tt), bs) <- solveLocalConstraints $ tInferExpr e
  let e'' = eLetB (eBinds bs) e'
  tCheckPatC' True tt p $ \ bsPat p' ->
    tcGuards ss $ \ rss ->
      let stmts = SBind p' e'' : rss
          stmts' = if null bsPat then stmts else SLet (eBinds bsPat) : stmts
      in ta stmts'
tcGuards (s:ss) ta = tcGuard s $ \ rs -> tcGuards ss $ \ rss -> ta (rs:rss)

tcGuard :: EStmt -> (EStmt -> T EAlt) -> T EAlt
tcGuard (SBind p e) ta = do
  --traceM ("tcGuard: " ++ show p ++ " <- " ++ show e)
  ((e', tt), bs) <- solveLocalConstraints $ tInferExpr e
  let e'' = eLetB (eBinds bs) e'
  -- tCheckPatC dicts used in solving in tcAlt
  tCheckPatC tt p $ \ p' -> ta (SBind p' e'')
tcGuard (SThen e) ta = do
  e' <- tCheckExprAndSolve (tBool (getSLoc e)) e
  ta (SThen e')
-- XXX do we have solves
tcGuard (SLet bs) ta = tcBinds bs $ \ bs' -> ta (SLet bs')
tcGuard (SRec ss) _ = tcError (getSLoc ss) "rec not allowed"

tcArm :: EType -> EType -> ECaseArm -> T ECaseArm
tcArm t tpat arm =
  case arm of
    -- The dicts introduced by tCheckPatC are
    -- used in the tCheckExprAndSolve in tcAlt.
    (p, alts) -> tCheckPatC tpat p $ \ pp -> do
      alts' <- tcAlts t alts
      return (pp, alts')

tCheckExprAndSolve :: HasCallStack => EType -> Expr -> T Expr
tCheckExprAndSolve t e = do
--  traceM $ "tCheckExprAndSolve: " ++ show (e, t)
  (e', bs) <- solveLocalConstraints $ tCheckExpr t e
  if null bs then
    return e'
   else
    return $ ELet (eBinds bs) e'

eBinds :: [(Ident, Expr)] -> [EBind]
eBinds ds = [Fcn i $ simpleEqn e | (i, e) <- ds]

addSolved :: [Solved] -> Eqn -> Eqn
addSolved ies (Eqn ps (EAlts as bs)) = Eqn ps (EAlts as (eBinds ies ++ bs))

instPatSigma :: HasCallStack =>
                 SLoc -> Sigma -> Expected -> T ()
instPatSigma loc pt (Infer r) = tSetRefType loc r pt
instPatSigma loc pt (Check t) = do { _ <- subsCheck loc undefined t pt; return () } -- XXX really?

subsCheck :: HasCallStack =>
              SLoc -> Expr -> Sigma -> Sigma -> T Expr
-- (subsCheck args off exp) checks that
-- 'off' is at least as polymorphic as 'args -> exp'
subsCheck loc exp1 sigma1 sigma2 = do -- Rule DEEP-SKOL
  (skol_tvs, rho2) <- skolemise sigma2
  exp1' <- subsCheckRho loc exp1 sigma1 rho2
  esc_tvs <- getFreeTyVars [sigma1,sigma2]
  let bad_tvs = filter (`elem` esc_tvs) skol_tvs
  unless (null bad_tvs) $
    tcErrorTK loc "Subsumption check failed"
  return exp1'

tCheckPatC' :: forall a . Bool -> EType -> EPat -> ([Solved] -> EPat -> T a) -> T a
tCheckPatC' _ t p@(EVar v) ta | not (isConIdent v) = do  -- simple special case
  withExtVals [(v, t)] $ ta [] p
tCheckPatC' solvePre t app ta = do
--  tcTrace $ "tCheckPatC: " ++ show app ++ " :: " ++ show t
  app' <- dsEFields app
  let vs = patVars app'
  multCheck vs
  env <- mapM (\ v -> (,) v <$> newUVar) vs
  withExtVals env $ do
    csOuter <- gets constraints
    putConstraints []
    (_sks, ds, pp) <- tCheckPat t app'
--    tcTrace ("tCheckPatC: " ++ show pp)
--    xt <- derefUVar t
--    tcTrace ("tCheckPatC ds=" ++ show ds ++ "t=" ++ show xt)
    -- XXX must check for leaking skolems
    bsPre <- if solvePre then solveConstraints else return []
    patCs <- gets constraints
    withDicts ds $ do
      patRest <- if null ds || null patCs
                 then return patCs
                 else do
                   let patUsed = allVarsExpr pp
                       canAutoSolve (di, ct) =
                         di `notElem` patUsed &&
                         case getAppM ct of
                           Just (iCls, _) -> iCls == mkIdent nameTypeEq
                           Nothing        -> False
                       (autoEqs, keepCs) = partition canAutoSolve patCs
                   if null autoEqs
                     then return patCs
                     else do
                       putConstraints autoEqs
                       _ <- solveConstraints
                       unEqs <- gets constraints
                       return (unEqs ++ keepCs)
      putConstraints (patRest ++ csOuter)
      ta bsPre pp

tCheckPatC :: forall a . EType -> EPat -> (EPat -> T a) -> T a
tCheckPatC t p ta = tCheckPatC' False t p (\ _ pp -> ta pp)

type EPatRet = ([TyVar], [(Ident, EConstraint)], EPat)  -- skolems, dictionaries, pattern

tCheckPat :: EType -> EPat -> T EPatRet
tCheckPat = tCheck tcPat
tInferPat :: EPat -> T (Typed EPatRet)
tInferPat = tInfer tcPat

-- XXX Has some duplication with tcExpr
tcPat :: Expected -> EPat -> T EPatRet
tcPat mt ae =
  let loc = getSLoc ae
      lit = tcPat mt (EViewPat (EApp (EVar (mkBuiltin loc "==")) ae) (eTrue loc))
      isNeg (EVar i) = i == mkBuiltin loc "negate"
      isNeg _ = False
  in
  case ae of
    EVar i | isDummyIdent i -> do
               -- _ can be anything, so just ignore it
               _ <- tGetExpType mt
               return ([], [], ae)
           | not (isConIdent i) -> do
               -- All pattern variables are in the environment as
               -- type references.  Assign the reference the given type.
               ext <- tGetExpType mt
               (p, t) <- tLookupV i
               unify loc t ext
               return ([], [], p)
           | otherwise -> tcPatAp mt [] ae
    EQVar _ _ -> tcPatAp mt [] ae
    EApp f _
           | isNeg f   -> lit            -- if it's (negate e) it must have been a negative literal
           | otherwise -> tcPatAp mt [] ae

    EOper e ies -> do e' <- tcOper e ies; tcPat mt e'

    ETuple es -> do
      let
        n = length es
      (xs, tes) <- mapAndUnzipM tInferPat es
      let
        (sks, ds, ees) = unzip3 xs
        ttup = tApps (tupleConstr loc n) tes
      munify loc mt ttup
      return (concat sks, concat ds, ETuple ees)

    EParen e -> tcPat mt e

    EListish (LList es) -> do
      te <- newUVar
      munify loc mt (tApp (tList loc) te)
      xs <- mapM (tCheckPat te) es
      case unzip3 xs of
        (sks, ds, es') -> return (concat sks, concat ds, EListish (LList es'))

    ELit _ _ -> lit

    ESign e t -> do
      typs <- gets typeTable
      let vs = freeTyVars [t] \\ getLocals typs
      mapM_ (\ v -> do kv <- newUVar; tv <- newUVar; extTypE v kv tv) vs
      t' <- tcType (Check kType) t >>= expandSyn
      instPatSigma loc t' mt
      tCheckPat t' e

    EAt i p -> do
      (_, ti) <- tLookupV i
      (sk, d, p') <- tcPat mt p
      munify loc mt ti
      return (sk, d, EAt i p')

    EViewPat e p -> do
      (e', ter) <-
        case mt of
          Infer _ -> do
            (e', te) <- tInferExpr e
            (tea, ter) <- unArrow loc te
            munify loc mt tea
            return (e', ter)
          Check tea -> do
            ter <- newUVar
            e' <- tCheckExpr (tea `tArrow` ter) e
            return (e', ter)
      (sk, d, p') <- tcPat (Check ter) p
      return (sk, d, EViewPat e' p')

    ELazy z p -> do
      (sk, d, p') <- tcPat mt p
      return (sk, d, ELazy z p')

    -- Allow C{} syntax even for non-records
    EUpdate p [] -> do
      (p', _) <- noEffect $ tInferExpr p
      let unApp n (EApp f _) = unApp (n+1) f  -- The constructor may have existential type, so strip the dictionaries.
          unApp n e = (n, e)
      case unApp 0 p' of
        (n, ECon c) -> tcPat mt $ eApps p (replicate (conArity c - n) eDummy)
        _      -> impossible
    EUpdate p isps -> do
      c <- fromMaybe impossible <$> getExprCon p
      tcPat mt =<< dsRecCon (const eDummy) c p isps

    EOr ps -> do
      let orFun = ELam noSLoc $ [ eEqn [p] true | p <- ps] ++ [ eEqn [eDummy] (eFalse loc) ]
          true = eTrue loc
      tcPat mt $ EViewPat orFun true

    _ -> error $ "tcPat: not handled " ++ prettyShow (getSLoc ae) ++ " " ++ showExpr ae

-- The expected type is for (eApps afn (reverse args))
tcPatAp :: HasCallStack =>
           Expected -> [EPat] -> EPat -> T EPatRet
--tcPatAp mt args afn | trace ("tcPatAp: " ++ show (mt, args, afn)) False = undefined
tcPatAp mt args afn =
  case afn of
    EVar i | isConIdent i -> do
      (con, xpt) <- tLookupV i
      tcPatApCon mt args con xpt

    EQVar con xpt -> tcPatApCon mt args con xpt

    EApp f a -> tcPatAp mt (a:args) f

    EParen e -> tcPatAp mt args e

    _ -> tcError (getSLoc afn) ("Bad pattern " ++ showExpr afn)

tcPatApCon :: Expected -> [EPat] -> EPat -> EType -> T EPatRet
tcPatApCon mt args con xpt = do
  let loc = getSLoc con
      nargs = length args
      checkArity ary | nargs < ary = tcError loc "too few arguments"
                     | nargs > ary = tcError loc "too many arguments"
                     | otherwise   = return ()
  case con of
    -- Pattern synonym
    ECon (ConSyn qi n (em, t)) -> do
      let e = case em of ETuple (e0 : _) -> e0; _ -> em
      checkArity n
      let (_, yes, _) = mkMatchDataTypeConstr (mkPatSynMatch qi) xpt
          vp = EViewPat (EQVar e t) (eApps yes args)
      --traceM ("patsyn " ++ show vp)
      tcPat mt vp

    -- Regular constructor
    _ -> do
      case xpt of
         -- Sanity check
         EForall _ _ EForall{} -> return ()
         _ -> impossiblePP con
      EForall _ avs apt <- tInst' xpt

      (sks, spt) <- shallowSkolemise avs apt
      (df, pf, pt) <-
        case getImplies spt of
          Nothing -> return ([], con, apt)
          Just (ctx, pt') -> do
            di <- newADictIdent loc
            return ([(di, ctx)], EApp con (EVar di), pt')

      let ary = arity pf
            where arity (ECon c) = conArity c
                  arity (EApp f _) = arity f - 1  -- deal with dictionary added above
                  arity e = impossiblePP e
      checkArity ary

      let step [] t r = return (t, r)
          step (a:as) t (sk, d, f) = do
            (at, rt) <- unArrow loc t
            (ska, da, a') <- tCheckPat at a
            step as rt (ska ++ sk, da ++ d, EApp f a')
      (tt, (skr, dr, pr)) <- step args pt (sks, df, pf)

      pp <- case mt of
              Check ext -> subsCheck loc pr ext tt
              Infer r   -> do { tSetRefType loc r tt; return pr }
      return (skr, dr, pp)

eTrue :: SLoc -> Expr
eTrue l = EVar $ mkBuiltin l "True"

eFalse :: SLoc -> Expr
eFalse l = EVar $ mkBuiltin l "False"

multCheck :: [Ident] -> T ()
multCheck vs =
  when (anySame vs) $ do
    let v = head vs
    tcError (getSLoc v) $ "Multiply defined: " ++ showIdent v

tcBinds :: HasCallStack =>
           [EBind] -> ([EBind] -> T a) -> T a
tcBinds axbs ta =
  withFixes [ (i, fx) | Infix fx is <- axbs, i <- is ] $ do
  xbs <- concat <$> mapM (dsPatBind <=< dsEFieldsBind) axbs
  let
    getSign (Sign is t) = do
      tt <- withTypeTable $ tCheckTypeTImpl QImpl kType t >>= expandSyn
      return [(is, tt)]
    getSign _ = return []
  -- find and check all type signatures
  istss <- mapM getSign xbs
  multCheck $ getBindsVars xbs
  let (sccs, signs) = sccDefs xbs
  withExtVals [ (i, t) | ists <- istss, (is, t) <- ists, i <- is ] $ do
    nbss <- mapM tcBindGrp sccs  -- Check a group of bindings, and extend symbol table
    nbs <- mapM tcBind signs     -- All types known, so check the bidings with signatures.
    ta (concat (nbs : nbss))

tcBindGrp :: SCC EBind -> T [EBind]
tcBindGrp (AcyclicSCC d) = tcBindGrp' [d]
tcBindGrp (CyclicSCC ds) = tcBindGrp' ds

tcBindGrp' :: [EBind] -> T [EBind]
tcBindGrp' bs = do
--  traceM $ "tcBindGrp start: " ++ show (getSLoc bs, bs)
  let def (Fcn i _) = do t <- newUVar; return (i, t)
      def d = impossiblePP d
  oldState <- get
  xts <- mapM def bs                    -- add temporary types
  extVals xts                           -- Extend the symbol table with the temporary types.
                                        -- These will be removed by the 'withExtVals' in 'tcBinds'
  bs' <- mapM tcBind bs                 -- type check bindings
  -- The contorted nested ifs are for efficiency.
  --   first test for monomorphism restriction (cheap),
  --   next test if there are any new type variables in the return type (a little more expensive),
  --   finally test for type variables in the environment (expensive).
  -- Ensure pattern bindings are not polymorphic
  let isDsPatBind (Fcn i _) = isPatBindVar i
      isDsPatBind _ = False
  if any isDsPatBind bs' then do
     return bs'
   else do
    fvs <- getMetaTyVars (map snd xts)  -- all unification variables used in return type
    let u = unique oldState             -- first of the new type variables
        qvs = filter (>= u) fvs         -- variables introduced for the group that can be quantified
--    traceM $ "tcBindGrp: " ++ show (bs', ts', qvs)
    if null qvs then                    -- no variables to generalize
      return bs'
     else do
      let envts = getEnvTypes' oldState -- types in scope outside the group
      envvs <- getMetaTyVars envts      -- all unification variables in the environment
      let qvs' = qvs \\ envvs
      if null qvs' then                 -- no variables to generalize
        return bs'
       else do
       -- Generalize
       cs0 <- gets constraints
       impTbl <- gets impEqTable
       cs <- mapM (derefUVar . snd) cs0
       -- find constraints involving the local tyvars
       let hasImpEq = any (\ (di, ct) -> isJust (M.lookup di impTbl) && not (null (intersect qvs' (metaTvs [ct])))) cs0
           ctx = nubBy eqEType $
                 filter (\ c -> not $ null $ intersect qvs' (metaTvs [c])) cs
       let multiParam ct =
             case getAppM ct of
               Just (_, as) -> length as /= 1
               -- Unknown head (e.g. flexible class variable):
               -- stay monomorphic rather than fail.
               Nothing -> True
       if hasImpEq ||
          any multiParam ctx ||       -- temporary workaround for
          -- Overloaded bind: fallback to monomorphic behavior
          not (null ctx) && not (all isSynFcn bs') then
         return bs'
        else do
--        traceM $ "tcBindGrp: u=" ++ show u ++ " xts=" ++ show xts ++ " ts'=" ++ show ts' ++ " cs=" ++ show cs
--        sub <- gets uvarSubst
--        traceM $ "  subst=" ++ show (IM.toList sub)
        -- Compute actual type signatures.
        -- Pattern bindings are treated specially.  A binding
        --   let (x, y) = foo z
        -- is translated to
        --   let pb$1 = foo z
        --       x = case pb$1 of (x, y) -> x
        --       y = case pb$1 of (x, y) -> y
        -- It's importand that pb$1 is only evaluated once, so
        -- we treat it as a mononorphic binding.
        let one (i, t) = do
              t' <- (generalizeType (getSLoc i) qvs' . addConstraints ctx) =<< derefUVar t
--              traceM $ "tcBindGrp generalize " ++ show (i, t')
              return (i, t')
        rxts <- mapM one xts
--        traceM $ "tcBindGrp done: txts=" ++ show rxts
--        traceM $ "tcBindGrp done: bs'=" ++ show bs'
        if null ctx then do
          -- There are no added constraints, so the results from tcBind are correct
--          traceM $ "tcBindGrp return"
          extVals rxts                        -- add correct types to the symbol table
          return bs'
         else do
          -- There are constraints, so we need to re-typecheck for dictionary insertion.
          -- First reset to state before type checking the group.
--          traceM $ "tcBindGrp redo"
          put oldState                        -- reset state, with old constraints
          extVals rxts                        -- add correct types to the symbol table
          mapM tcBind bs                      -- and type check again

-- Is this syntactically a function?
isSynFcn :: EBind -> Bool
isSynFcn (Fcn _ (Eqn (_:_) _ : _)) = True
isSynFcn _ = False

generalizeType :: SLoc -> [TRef] -> EType -> T EType
generalizeType loc vs t = noEffect $ do           -- ignore the setUVar done in here
  let is = map (\ v -> mkIdentSLoc loc ('a':show v)) (metaTvs [t] `intersect` vs)
  zipWithM_ (\ v i -> setUVar v (EVar i)) vs is   -- make real type variables
  t' <- derefUVar t                               -- and substitute those
  return $ eForall' QImpl (map (`IdKind` EVar dummyIdent) is) t'

-- Temporarily extend the fixity table
withFixes :: [FixDef] -> T a -> T a
withFixes [] ta = ta
withFixes fixs ta = do
  oft <- gets fixTable
  modify $ \ st -> st{ fixTable = foldr (uncurry M.insert) oft fixs }
  a <- ta
  modify $ \ st -> st{ fixTable = oft }
  return a

tcBind :: EBind -> T EBind
tcBind abind =
  case abind of
    Fcn i eqns -> do
      (_, tt) <- tLookupV i
      teqns <- tcEqns False tt eqns
      return $ Fcn i teqns
    _ -> return abind

-- Desugar [T] and (T,T,...)
dsType :: EType -> EType
dsType at =
  case at of
    EVar _ -> at
    EApp f a -> EApp (dsType f) (dsType a)
    EOper t ies -> EOper (dsType t) [(i, dsType e) | (i, e) <- ies]
    EListish (LList []) -> EVar (mkIdentSLoc (getSLoc at) "'[]")
    EListish (LList [t]) -> tApp (tList (getSLoc at)) (dsType t)
    ETuple ts -> tApps (tupleConstr (getSLoc at) (length ts)) (map dsType ts)
    EParen t -> dsType t
    ESign t k -> ESign (dsType t) k
    EForall b iks t -> EForall b iks (dsType t)
    ELit _ (LStr _) -> at
    ELit _ (LInteger _) -> at
    EQVar _ _ -> at
    _ -> impossiblePP at

tListI :: SLoc -> Ident
tListI loc = mkIdentSLoc loc nameList

tList :: SLoc -> EType
tList = tCon . tListI

tBool :: SLoc -> EType
tBool loc = tConI loc $ boolPrefix ++ "Bool"

showTModule :: forall a . (a -> String) -> TModule a -> String
showTModule sh amdl = "Tmodule " ++ showIdent (tModuleName amdl) ++ "\n" ++ sh (tBindingsOf amdl) ++ "\n"

-----------------------------------------------------

getFreeTyVars :: [EType] -> T [TyVar]
getFreeTyVars tys = do
  tys' <- mapM derefUVar tys
  return (freeTyVars tys')

getMetaTyVars :: [EType] -> T [TRef]
getMetaTyVars tys = do
  tys' <- mapM derefUVar tys
  return (metaTvs tys')

getEnvTypes :: T [EType]
getEnvTypes = gets getEnvTypes'

getEnvTypes' :: TCState -> [EType]
getEnvTypes' = map entryType . stElemsLcl . valueTable

tyVarSubst :: [a] -> EType -> ([IdKind], [(a, EType)])
tyVarSubst tvs ty =
  let usedVars = allVarsExpr ty -- Avoid used type variables
      newVars = take (length tvs) (allBinders \\ usedVars)
      newVarsK = map (\ i -> IdKind i noKind) newVars
      noKind = eDummy
  in  (newVarsK, zipWith (\ tv n -> (tv, EVar n)) tvs newVars)

-- Quantify over the specified type variables.
-- The type should be zonked.
quantify :: [TRef] -> Rho -> T Sigma
quantify [] ty = return ty
quantify tvs ty = do
  let (newVarsK, sub) = tyVarSubst tvs ty
  osubst <- gets uvarSubst
  mapM_ (uncurry setUVar) sub
  ty' <- derefUVar ty
  putUvarSubst osubst  -- reset the setUVar we did above
  return (EForall QImpl newVarsK ty')

-- Skolemize the given variables
shallowSkolemise :: [IdKind] -> EType -> T ([TyVar], EType)
shallowSkolemise tvs ty = do
  sks <- mapM (newSkolemTyVar . idKindIdent) tvs
  return (sks, subst (zip (map idKindIdent tvs) (map EVar sks)) ty)

skolemise :: HasCallStack =>
             Sigma -> T ([TyVar], Rho)
-- Performs deep skolemisation, returning the
-- skolem constants and the skolemised type.
skolemise (EForall _ tvs ty) = do -- Rule PRPOLY
  (sks1, ty') <- shallowSkolemise tvs ty
  (sks2, ty'') <- skolemise ty'
  return (sks1 ++ sks2, ty'')
skolemise t@(EApp _ _) | Just (arg_ty, res_ty) <- getArrow t = do
  (sks, res_ty') <- skolemise res_ty
  return (sks, arg_ty `tArrow` res_ty')
skolemise (EApp f a) = do
  (sks1, f') <- skolemise f
  (sks2, a') <- skolemise a
  return (sks1 ++ sks2, EApp f' a')
skolemise ty =
  return ([], ty)

-- Skolem tyvars are just identifiers that start with a uniq
newSkolemTyVar :: Ident -> T Ident
newSkolemTyVar tv = do
  uniq <- newUniq
  return (mkIdentSLoc (getSLoc tv) (unIdent tv ++ "#" ++ show uniq))

metaTvs :: [EType] -> [TRef]
-- Get the MetaTvs from a type; no duplicates in result
metaTvs tys = foldr go [] tys
  where
    go (EUVar tv) acc
      | tv `elem` acc = acc
      | otherwise = tv : acc
    go (EVar _) acc = acc
    go (EForall _ _ ty) acc = go ty acc
    go (EApp fun arg) acc = go fun (go arg acc)
    go (ELit _ _) acc = acc
    go _ _ = impossible

{-
inferSigma :: Expr -> T (Expr, Sigma)
inferSigma e = do
  (e', exp_ty) <- inferRho e
  env_tys      <- getEnvTypes
  env_tvs      <- getMetaTyVars env_tys
  res_tvs      <- getMetaTyVars [exp_ty]
  let forall_tvs = res_tvs \\ env_tvs
  (e',) <$> quantify forall_tvs exp_ty
-}

checkSigma :: HasCallStack =>
              Expr -> Sigma -> T Expr
checkSigma expr sigma = do
  (skol_tvs, rho) <- skolemise sigma
--  sigma' <- derefUVar sigma
--  tcTrace $ "**** checkSigma: " ++ show expr ++ " :: " ++ show sigma ++ " = " ++ show sigma' ++ " " ++ show skol_tvs
  expr' <- tCheckExpr rho expr
  if null skol_tvs then
    -- Fast special case
    return expr'
   else do
    env_tys <- getEnvTypes
    esc_tvs <- getFreeTyVars (sigma : env_tys)
    let bad_tvs = filter (`elem` esc_tvs) skol_tvs
    unless (null bad_tvs) $
      tcErrorTK (getSLoc expr) $ "not polymorphic enough: " ++ unwords (map showIdent bad_tvs)
    return expr'

subsCheckRho :: HasCallStack =>
                SLoc -> Expr -> Sigma -> Rho -> T Expr
--subsCheckRho _ e1 t1 t2 | trace ("subsCheckRho: " ++ show e1 ++ " :: " ++ show t1 ++ " = " ++ show t2) False = undefined
-- XXX Is this even right?  It's not part of the paper.
subsCheckRho loc exp1 (EForall _ vs1 t1) (EForall _ vs2 t2) | length vs1 == length vs2 = do
  let sub = [(v1, EVar v2) | (IdKind v1 _, IdKind v2 _) <- zip vs1 vs2]
  unify loc (subst sub t1) t2
  return exp1
subsCheckRho loc exp1 sigma1@EForall{} rho2 = do -- Rule SPEC
  (exp1', rho1) <- tInst exp1 sigma1
  subsCheckRho loc exp1' rho1 rho2
subsCheckRho loc exp1 arho1 rho2 | Just _ <- getImplies arho1 = do
  (exp1', rho1) <- tInst exp1 arho1
  subsCheckRho loc exp1' rho1 rho2
subsCheckRho loc exp1 rho1 rho2 | Just (a2, r2) <- getArrow rho2 = do -- Rule FUN
  rho1' <- derefUVar rho1
  case rho1' of
    -- Not an arrow, unify the whole types so a mismatch reports both.
    EVar _   -> unify loc rho1' rho2 >> return exp1
    EApp _ _ | Nothing <- getArrow rho1' -> unify loc rho1' rho2 >> return exp1
    _ -> do
      (a1, r1) <- unArrow loc rho1'
      subsCheckFun loc exp1 a1 r1 a2 r2
subsCheckRho loc exp1 rho1 rho2 | Just (a1, r1) <- getArrow rho1 = do -- Rule FUN
  rho2' <- derefUVar rho2
  case rho2' of
    -- Not an arrow, unify the whole types so a mismatch reports both
    -- (and in the right order, unArrow would treat rho2 as the actual type).
    EVar _   -> unify loc rho1 rho2' >> return exp1
    EApp _ _ | Nothing <- getArrow rho2' -> unify loc rho1 rho2' >> return exp1
    _ -> do
      (a2,r2) <- unArrow loc rho2'
      subsCheckFun loc exp1 a1 r1 a2 r2
subsCheckRho loc exp1 tau1 tau2 = do  -- Rule MONO
--  tcTrace $ "subsCheckRho: MONO " ++ show (tau1, tau2)
  unify loc tau1 tau2 -- Revert to ordinary unification
  return exp1

subsCheckFun :: HasCallStack =>
                SLoc -> Expr -> Sigma -> Rho -> Sigma -> Rho -> T Expr
subsCheckFun loc e1 a1 r1 a2 r2 = do
  _ <- subsCheck loc eCannotHappen a2 a1   -- XXX
  subsCheckRho loc e1 r1 r2

instSigma :: HasCallStack =>
             SLoc -> Expr -> Sigma -> Expected -> T Expr
instSigma loc e1 t1 (Check t2) = do
  --tcTrace ("instSigma: Check e1=" ++ show e1 ++ " t1=" ++ showEType t1 ++ " t2=" ++ showEType t2)
  subsCheckRho loc e1 t1 t2
instSigma loc e1 t1 (Infer r) = do
  --tcTrace ("instSigma: Infer e1=" ++ show e1 ++ " t1=" ++ showEType t1 ++ " r=" ++ show r)
  (e1', t1') <- tInst e1 t1
  --tcTrace ("instSigma: Infer " ++ showEType t1 ++ " ==> " ++ showEType t1')
  tSetRefType loc r t1'
  return e1'

eCannotHappen :: Expr
eCannotHappen = --undefined
                EVar $ mkIdent "cannot-happen"

-----

--
-- Pattern synonyms look like
--   pattern P :: forall a1...an . ctxr => forall b1...bm . ctxp => t1 -> ... -> ti -> t
--   pattern P x1...xi <- p where P = e
-- (this type is the canonicalized type, generated by canonPatSynType).
-- The synonym is translated into a builder, a matcher and a type.
-- Each synonym use is replaced by a simple view pattern.
--
-- The builder is simple.  It gets the same name and type as the pattern synonym,
-- and the definition is the one provided in the definition.
--   P :: forall a1...an . ctxr => forall b1...bm . ctxp => t1 -> ... ti -> t
--   P = e
--
-- The matcher needs to account for possible existentials so we get a data type
-- for the match result that can have existentials.
--   data P%T a1...an = forall b1...bm . ctxp => M t1 ... ti
--                    | N
--
-- The matcher itself has the required part of the synonym type, whereas
-- the provided part is in the data type.  The matcher simply matches on the given pattern.
--   P% :: forall a1...an . ctxr => t -> P%T a1...an
--   P% p = M x1...xi
--   P% _ = N
-- So when the synonym P matches the matcher P% will return the M constructor
-- of the P%T type, and then N constructor when there is no match.
--
-- Each use of the pattern synonym
--   P p1...pi
-- is replaced by
--   (P% -> M p1...pi)
--
-- The data type, P%T, is not entered into any symbol tables.
-- The matcher, P%, is in the symbol table, but is not part of the exported symbols.
-- The transformed expression simply carries enough information about the types
-- (using EQVar).  The exported ECon for P has this information.
--

emptyCtx :: EConstraint
emptyCtx = EVar $ tupleConstr noSLoc 0

isEmptyCtx :: EConstraint -> Bool
isEmptyCtx (EVar i) = i == tupleConstr noSLoc 0
isEmptyCtx _ = False

-- Expand a pattern synonym into the builder, matcher, and any record selector definitions.
-- Removes the actual pattern definition.
expandPatSyn :: EDef -> T [EDef]
expandPatSyn (Pattern (i, vks) p me) = do
  (_, t) <- tLookup "type signature" i
  (im, qim) <- addPatSynMatch i t
  let (ddata, yes, no) = mkMatchDataTypeConstr qim t
      mexp = fmap (Fcn i) me
      pat = Fcn im [ eEqn [p] match
                   , eEqn [eDummy] no]
      match = eApps yes (map (EVar . idKindIdent) vks)
      dname = case ddata of Data (n, _) _ _ -> n; _ -> impossible
      fs = recPatFields vks
      (_vks1, _ctx1, vks2, _ctx2, ty) = splitPatSynType t
      (ats, _rt) = getArrows ty
      evs = map idKindIdent vks2
      n = length ats
      selFcns =
        [ Fcn fld [ eEqn [eApps (EVar i) [ if j == k then EVar v else eDummy | j <- [0 .. n - 1] ]] (EVar v) ]
        | (k, (fld, fty)) <- zip [0 :: Int ..] (zip fs ats)
        , null (freeTyVars [fty] `intersect` evs)
        , let v = mkIdentSLoc (getSLoc fld) "$sel"
        ]
  kvar <- newUVar    -- We don't care about the kind
  withTypeTable $ extValQTop dname kvar
  pure $ maybeToList mexp ++ [pat, ddata] ++ selFcns
expandPatSyn d = pure [d]

-- Add the matcher for a pattern synonym to the symbol table.
-- Return the added identifier.
addPatSynMatch :: Ident -> EType -> T (Ident, Ident)
addPatSynMatch i at = do
  mn <- gets moduleName
  let ip = mkPatSynMatch i
      qip = qualIdent mn ip
  extValETop ip (mkPatSynMatchType qip at) (EVar qip)
  return (ip, qip)

mkPatSynMatchType :: Ident -> EType -> EType
mkPatSynMatchType qip at =
  let (vks1, ctx1, _vks2, _ctx2, ty) = splitPatSynType at
      (_ats, rt) = getArrows ty
      pstycon = mkMatchDataTypeName qip
  in  eForall vks1 $ etImplies ctx1 $ rt `tArrow` tApps pstycon (map (EVar . idKindIdent) vks1)

-- Given the (qualified) name of a synonym and its type generate:
-- match-constructor, nomatch-constructor
mkMatchDataTypeConstr :: HasCallStack => Ident -> EType -> (EDef, Expr, Expr)
mkMatchDataTypeConstr qi at =
  let (vks1, _ctx1, vks2, ctx2, ty) = splitPatSynType at
      (ats, _rt) = getArrows ty
      n = length ats
      mi = addIdentSuffix qi "M"
      ni = addIdentSuffix qi "N"
      cti = [ (mi, n + if isEmptyCtx ctx2 then 0 else 1), (ni, 0) ]
      conm = ConData cti mi []
      conn = ConData cti ni []
      tycon = mkMatchDataTypeName qi
      tr = tApps tycon $ map (EVar . idKindIdent) vks1
      tn = EForall QExpl vks1 $ EForall QExpl [] tr
      tm = EForall QExpl vks1 $ EForall QExpl vks2 $ etImplies ctx2 $ foldr tArrow tr ats

      ddata = Data lhs [cm, cn] []
            where lhs = (unQualIdent tycon, vks1)
                  cm = Constr vks2 (if isEmptyCtx ctx2 then [] else [ctx2]) (unQualIdent mi) False (Left $ map ((,) False) ats)
                  cn = Constr []   []                                       (unQualIdent ni) False (Left [])

  in  -- trace ("M :: " ++ show tm ++ ",  N :: " ++ show tn) $
      -- trace (showEDefs [ddata]) $
      (ddata, EQVar (ECon conm) tm, EQVar (ECon conn) tn)

mkPatSynMatch :: Ident -> Ident
mkPatSynMatch i = addIdentSuffix i "%"

mkMatchDataTypeName :: Ident -> Ident
mkMatchDataTypeName i = addIdentSuffix i "T"

isMatchDataTypeName :: Ident -> Bool
isMatchDataTypeName = isSuffixOf "%T" . unIdent

-- A pattern synonym always has a type of the form
--  forall vs1 . ctx1 => forall vs2 . ctx2 => ty
--         required             provided
-- The input has forall inserted, but the implicit forall
-- may be in the wrong place.
canonPatSynType :: EType -> T EType
canonPatSynType at0 = do
  at <- expandSyn at0
  let mkTyp rVks rCtx pVks pCtx ty =
        EForall QExpl rVks $ tImplies rCtx $
        EForall QExpl pVks $ tImplies pCtx ty
      getImplies' :: EType -> (EConstraint, EType)
      getImplies' ty = fromMaybe (emptyCtx, ty) $ getImplies ty

  case at of
    EForall QImpl vks t0 -> do
      -- Implicit forall, the xs need to be split between required and provided.
      let (reqCtx, t1) = getImplies' t0
          (proCtx, t2) = getImplies' t1
          proVs = freeTyVars [proCtx]
          (proVks, reqVks) = partition ((`elem` proVs) . idKindIdent) vks
--      traceM "%%% implicit"
      pure $ mkTyp reqVks reqCtx proVks proCtx t2

    EForall _ reqVks t0 -> do   -- QExpl/QReqd
      -- Explicit forall
      let (reqCtx, t1) = getImplies' t0
          (proVks, t2) = unForall t1
          (proCtx, t3) = getImplies' t2
--      traceM "%%% explicit"
      pure $ mkTyp reqVks reqCtx proVks proCtx t3

    ty -> do
      -- No forall at all (e.g. nullary constraint like HasCallStack => A -> B).
      let (reqCtx, t1) = getImplies' ty
          (proVks, t2) = unForall t1
          (proCtx, t3) = getImplies' t2
      pure $ mkTyp [] reqCtx proVks proCtx t3

splitPatSynType :: EType -> ([IdKind], EConstraint, [IdKind], EConstraint, EType)
splitPatSynType (EForall _ vks1 t0)
  | Just  (ctx1, EForall _ vks2 t1) <- getImplies t0
  , Just  (ctx2, ty) <- getImplies t1
  = (vks1, ctx1, vks2, ctx2, ty)
splitPatSynType t = impossiblePP t

-----

-- Given a dictionary of a (constraint type), split it up
--  * components of a tupled constraint
--  * superclasses of a constraint
expandDict :: HasCallStack => Expr -> EConstraint -> T [InstDictC]
expandDict edict ct = expandDict' 0 [] [] edict ct

-- Bound on superclass expansion depth.  Guards against infinite
-- regress with recursive superclasses through stuck families, e.g.
--   class IsPass (NoGhcTcPass p) => IsPass (p :: Pass)
-- where expanding IsPass p yields IsPass (NoGhcTcPass p), whose
-- superclass is IsPass (NoGhcTcPass (NoGhcTcPass p)), and so on.
maxSuperDepth :: Int
maxSuperDepth = 8

expandDict' :: HasCallStack => Int -> [IdKind] -> [EConstraint] -> Expr -> EConstraint -> T [InstDictC]
expandDict' depth avks actx edict acc0 = do
  acc <- normConstraint acc0
  let
    (bvks, bctx, cc) = splitContext acc
    (iCls, args) = getApp cc
    vks = avks ++ bvks
    ctx = actx ++ bctx
  case getTupleConstr iCls of
    Just _ -> do
      concat <$> mapM (\ (i, a) -> expandDict' depth vks ctx (mkTupleSel i (length args) `EApp` edict) a) (zip [0..] args)
    Nothing -> do
      ct <- gets classTable
      case M.lookup iCls ct of
        Nothing -> do
          -- if iCls is a variable it's not in the class table, otherwise it's an error
          when (isConIdent iCls) $
            --impossible
            -- XXX it seems we can get here, e.g., Control.Monad.Fail without Applicative import
            impossiblePP (acc, iCls)
          return [(edict, vks, ctx, cc, [])]
        Just (ClassInfo iks sups _ _ fds) -> do
          let
            vs = map idKindIdent iks
            sub = zip vs args
            sups' = map (subst sub) sups
          insts <- if depth >= maxSuperDepth then return []
                   else concat <$> mapM (\ (i, sup) -> expandDict' (depth + 1) vks ctx (EVar (mkSuperSel iCls i) `EApp` edict) sup) (zip [1 ..] sups')
          return $ (edict, vks, ctx, cc, fds) : insts

mkSuperSel :: HasCallStack =>
              Ident -> Int -> Ident
mkSuperSel c i = addIdentSuffix c ("$super" ++ show i)

---------------------------------

type Solved = (Ident, Expr)

-- XXX
-- solveLocalConstraints is wrong; it tries to solve before everything is known.
-- Example:
--  class MArray a m where
--    op1 :: m a
--    op2 :: a -> m ()
--
--  foo :: forall a m . (Monad m, MArray a m) => m a
--  foo = do
--    aa <- op1
--    let f :: forall mm . (MArray a mm) => mm ()
--        f = op2 aa
--    return aa
-- When solving for f we don't know yet aa has type a (it's a unification variable).
-- So it cannot be solved yet.

-- Solve constraints generated locally in 'ta'.
-- Keep any unsolved ones for later.
solveLocalConstraints :: forall a . T a -> T (a, [Solved])
solveLocalConstraints ta = do
  cs <- gets constraints           -- old constraints
  putConstraints []                -- start empty
  a <- ta                          -- compute, generating constraints
  ds <- solveConstraints           -- solve those
  un <- gets constraints           -- get remaining unsolved
--  traceM $ "solveLocalConstraints: " ++ show (cs, ds, un)
  putConstraints (un ++ cs)        -- put back unsolved and old constraints
  return (a, ds)

solveAndDefault :: forall a . Bool -> T a -> T (a, [Solved])
solveAndDefault False ta = solveLocalConstraints ta
solveAndDefault True  ta = do
  a <- ta
  ds <- solveConstraints
  dsCo <- defaultCoercibleTyVars
  cs <- gets constraints
  vs <- getMetaTyVars (map snd cs)    -- These are the type variables that need defaulting
--  tcTrace $ "solveAndDefault: meta=" ++ show vs
  -- XXX may have to iterate this with fundeps
  ds' <- concat <$> mapM defaultOneTyVar vs
  return (a, ds ++ dsCo ++ ds')

defaultCoercibleTyVars :: T [Solved]
defaultCoercibleTyVars = do
  cs <- gets constraints
  dt <- gets dataTable
  cs' <- mapM (\(di, ct) -> (,) di <$> derefUVar ct) cs
  let coImps =
        [ (isJust (unwrapTopNewtype dt (if isEUVar a then b else a)), (getSLoc di, a, b))
        | (di, ct) <- cs'
        , Just (c, [a, b]) <- [getAppM ct]
        , c == mkIdent nameCoercible
        , isEUVar a /= isEUVar b
        ]
  case ([ x | (True, x) <- coImps ] ++ [ x | (False, x) <- coImps ]) of
    (l, a, b) : _ -> do
      unify l a b
      ds1 <- solveConstraints
      ds2 <- defaultCoercibleTyVars
      return (ds1 ++ ds2)
    [] -> return []

defaultOneTyVar :: TRef -> T [Solved]
defaultOneTyVar tv = do
--  traceM $ "defaultOneTyVar: " ++ show tv
  old <- get             -- get entire old state
  let cvs = nub [ c | (_, EApp (EVar c) (EUVar tv')) <- constraints old, tv == tv' ]  -- all C v constraints
--  traceM $ "defaultOneTyVar: cvs = " ++ show cvs
  dvs <- getSuperClasses cvs                            -- add superclasses
--  traceM $ "defaultOneTyVar: dvs = " ++ show dvs
  let oneCls c | Just ts <- M.lookup c (defaults old) =
        take 1 $ filter (\ t -> all (\ cc -> soluble cc t) cvs) ts
               | otherwise = []
      soluble c t = fst $ flip tcRun old $ do
        putConstraints [(dummyIdent, EApp (EVar c) t)]  -- Use current (C T) constraint
        _ <- solveConstraints                           -- and solve.
        cs <- gets constraints
        return $ null cs                                -- No constraints left?
      tys = nubBy eqEType $ concatMap oneCls dvs
--  traceM $ "defaultOneTyVar: " ++ show (tv, tys)
  case tys of
    [ty] -> do            -- There is a single type solving everything
      setUVar tv ty
      solveConstraints
    _ -> return []        -- Nothing solved

-- The transitive closure of super-classes.
-- XXX Somewhat duplicated with expandDict
getSuperClasses :: [Ident] -> T [Ident]
getSuperClasses ais = do
  ct <- gets classTable
  let loop done [] = done
      loop done (i:is) | i `elem` done = loop done is
                       | otherwise = i :
        case M.lookup i ct of
          -- Unknown class (e.g. a class variable from a
          -- variable-headed constraint): it has no known
          -- superclasses, but keep it in the result.
          Nothing -> loop (i:done) is
          Just (ClassInfo _ supers _ _ _) ->
            loop (i:done) (concatMap flatten supers ++ is)
      flatten a =
        case getApp a of
          (c, ts) ->
            case getTupleConstr c of
              Nothing -> [c]
              Just _ -> concatMap flatten ts
  return $ loop [] ais

{-
showInstInfo :: InstInfo -> String
showInstInfo (InstInfo m ds fds) = "InstInfo " ++ show (M.toList m) ++ " " ++ showListS showInstDict ds ++ show fds

showInstDict :: InstDict -> String
showInstDict (InstDict e ctxts) = showExpr e ++ " :: " ++ prettyShow (addConstraints ctx (tApps (mkIdent "_") ts))
  where (ctx, ts) = ctxts 10000

showInstDef :: (Ident, InstInfo) -> String
showInstDef (cls, InstInfo m ds _) = "instDef " ++ show cls ++ ": "
            ++ show (M.toList m) ++ ", " ++ showListS showInstDict ds

showMatch :: (Expr, [EConstraint], [Improve]) -> String
showMatch (e, ts, _) = show e ++ " " ++ show ts

showConstraint :: (Ident, EConstraint) -> String
showConstraint (i, t) = show i ++ " :: " ++ show t
-}

type Goal = (Ident, EType)     -- What we want to solve
type UGoal = Goal              -- Unsolved goal
type Soln = (Ident, Expr)      -- Solution, i.e., binding of a dictionary
type Improve = (SLoc, EType, EType)  -- Unify to get an improvement substitution

-- Solve as many constraints as possible.
-- Return bindings for the dictionary witnesses.
solveConstraints :: T [Soln]
solveConstraints = do
  cs <- gets constraints
  if null cs then
    return []
   else do
    addMetaDicts
--    tcTrace "------------------------------------------\nsolveConstraints"
    -- Normalize with given type equalities AND given family equalities
    -- (rewriting stuck family applications), so goals like
    -- Anno (IdGhcP p) unify once (Anno (IdGhcP p) ~ SrcSpanAnnN) is given.
    cs' <- mapM (\ (i,t) -> (,) i <$> normConstraint t) cs
    let isEqGoal (_, ct) = case getAppM ct of
                             Just (iCls, _) -> iCls == mkIdent nameTypeEq
                             Nothing        -> False
        (eqGoals, clsGoals) = partition isEqGoal cs'
    (unsEq, solEq, impEq) <- solveMany eqGoals [] [] []
    if not (null impEq) then do
      putConstraints (unsEq ++ clsGoals)
      mapM_ (\ (l, a, b) -> unify l a b) impEq
      (solEq ++) <$> solveConstraints
     else do
--    tcTrace ("constraints:\n" ++ unlines (map showConstraint cs'))
      (unsolved, solved, improves) <- solveMany (clsGoals ++ unsEq) [] [] []
      putConstraints unsolved
--    tcTrace ("solved:\n"   ++ unlines [ showIdent i ++ " = "  ++ showExpr  e | (i, e) <- solved ])
--    tcTrace ("unsolved:\n" ++ unlines [ showIdent i ++ " :: " ++ showEType t | (i, t) <- unsolved ])
      if null improves then
        return (solEq ++ solved)
       else do
        -- We have improving substitutions.
        -- Do the unifications, and try to solve more.
        mapM_ (\ (l, a, b) -> unify l a b) improves
        (++ (solEq ++ solved)) <$> solveConstraints

-- A solver get a location, class&types (i.e. (C t1 ... tn)),
-- and, if successful, returns a dictionary expression and new goals.
type SolveOne = SLoc -> Ident -> [EType] -> T (Maybe (Expr, [Goal], [Improve]))

-- Table of constraint solvers.
-- The predicate gets the class name and picks a solver.
-- There must always by at least one solver that matches
solvers :: [(Ident -> Bool, SolveOne)]
solvers =
  [ (isJust . getTupleConstr,            solveTuple)        -- handle tuple constraints, i.e. (C1 t1, C2 t2, ...)
  , ((== mkIdent nameTypeEq),            solveTypeEq)       -- handle equality constraints, i.e. (t1 ~ t2)
  , ((== mkIdent nameKnownNat),          solveKnownNat)     -- KnownNat 123 constraints
  , ((== mkIdent nameKnownSymbol),       solveKnownSymbol)  -- KnownSymbol "abc" constraints
  , ((== mkIdent nameCoercible),         solveCoercible)    -- Coercible a b constraints
  , ((== identDataTypeableTypeable),     solveTypeable)     -- Typeable Symbol/Nat/promoted-con constraints
  , (const True,                         solveInst)         -- handle constraints with instances
  ]

-- Examine each goal, either solve it (possibly producing new goals) or let it remain unsolved.
solveMany :: [Goal] -> [UGoal] -> [(EType, Soln)] -> [Improve] -> T ([UGoal], [Soln], [Improve])
solveMany [] uns sol imp = return (uns, map snd sol, imp)
solveMany ((di, ct) : cnss) uns sol imp | Just (_, (dd, _)) <- find (eqEType ct . fst) sol =
  solveMany cnss uns ((ct, (di, EVar dd)) : sol) imp
-- Need to handle ct of the form C => T, and forall a . T
solveMany (cns@(di, ct) : cnss) uns sol imp = do
--  tcTrace ("solveMany: trying " ++ showEType ct)
  let loc = getSLoc di
  impTbl <- gets impEqTable
  ads0 <- gets argDicts
  ads <- mapM (\ (ai, act) -> (,) ai <$> normConstraint act) ads0
  -- Givens captured when this dictionary was created (e.g. GADT pattern
  -- equalities in scope at the use site).  Subgoals inherit them so the
  -- givens thread down the instance resolution chain.
  let cap = M.lookup di impTbl
      propagate gs =
        case cap of
          Nothing -> return ()
          Just cp -> modify $ \ ts -> ts { impEqTable = foldr (\ (gi, _) m -> M.insert gi cp m) (impEqTable ts) gs }
      -- The normal path failed: retry once with the captured givens
      -- applied.  On failure keep the ORIGINAL goal for a later pass,
      -- once more unification variables have been settled.
      retryImp =
        case cap of
          Nothing -> solveMany cnss (cns : uns) sol imp
          Just (capEqs, capFeqs) -> do
            ctImp <- normWithGivens capEqs capFeqs ct
            if ctImp `eqEType` ct then
              solveMany cnss (cns : uns) sol imp
             else do
              mres <- tryImpGoal loc ctImp ads
              case mres of
                Nothing -> solveMany cnss (cns : uns) sol imp
                Just (de, gs, is) -> do
                  propagate gs
                  gs' <- mapM (\ (gi, gt) -> (,) gi <$> normConstraint gt) gs
                  solveMany (gs' ++ cnss) uns ((ct, (di, de)) : sol) (is ++ imp)
  -- Check if we have an exact match among the arguments dictionaries.
  -- This is important to find tupled dictionaries in recursive calls.
  -- This runs before any captured-given rewriting so outer dictionaries
  -- (e.g. an outer Show a) keep priority.
  case [ ai | (ai, act) <- ads, ct `eqEType` act ] of
    ai : _ -> do
--      tcTrace $ "solve with arg " ++ show ct
      solveMany cnss uns ((ct, (di, EVar ai)) : sol) imp
    [] -> do
      case getAppM ct of
        -- The head of the goal is not (yet) known.  This happens with
        -- variable-headed constraints, e.g. goal (_c (Maybe _a)) from
        -- instantiating (c (Maybe a)).  Try to match a local given up
        -- to substitution; if none matches, leave the goal unsolved in
        -- hope that the head gets resolved later.  Either way, do not fail here.
        Nothing ->
          case matchFlexGoal loc ct ads of
            Just (ai, is) -> solveMany cnss uns ((ct, (di, EVar ai)) : sol) (is ++ imp)
            Nothing       -> retryImp
        Just (iCls, cts) -> do
          let solver = head [ s | (p, s) <- solvers, p iCls ]
          msol <- solver loc iCls cts
--          tcTrace ("solveMany msol=" ++ show msol)
          case msol of
            Nothing           -> retryImp
            Just (de, gs, is) -> do
              propagate gs
              gs' <- mapM (\ (gi, gt) -> (,) gi <$> normConstraint gt) gs
              solveMany (gs' ++ cnss) uns ((ct, (di, de)) : sol) (is ++ imp)

-- Normalize a goal with captured givens: rewrite with the captured type
-- equalities and expand synonyms/stuck families using the captured family
-- equalities in front of the current ones.
normWithGivens :: TypeEqTable -> [(EType, EType)] -> EType -> T EType
normWithGivens capEqs capFeqs t = do
  t0 <- derefUVar t
  syns <- gets synTable
  feqs <- gets famEqTable
  let allFeqs = if null capFeqs then feqs else capFeqs ++ feqs
      step x = normTypeEq capEqs (expandSynFull syns allFeqs (normTypeEq capEqs x))
      t1 = step t0
  return $ if t1 `eqEType` t0 then t1 else step t1

-- Solve a goal rewritten with captured givens, checking the outer argument
-- dictionaries first so they keep priority over the rewriting.
tryImpGoal :: SLoc -> EConstraint -> [(Ident, EConstraint)] -> T (Maybe (Expr, [Goal], [Improve]))
tryImpGoal loc ctImp ads =
  case [ ai | (ai, act) <- ads, ctImp `eqEType` act ] of
    ai : _ -> return (Just (EVar ai, [], []))
    [] ->
      case getAppM ctImp of
        Nothing ->
          case matchFlexGoal loc ctImp ads of
            Just (ai, is) -> return (Just (EVar ai, [], is))
            Nothing       -> return Nothing
        Just (iCls, cts) -> do
          let solver = head [ s | (p, s) <- solvers, p iCls ]
          solver loc iCls cts

-- Match a goal whose head is a unification variable (from a
-- variable-headed constraint like (c t)) against the local givens.
-- Succeeds when some given matches the goal up to substitution of the
-- goal's unification variables, e.g. goal (_c (Maybe _a)) against
-- given (C (Maybe b)) with [_c := C, _a := b].
-- Returns the given dictionary and the improving substitution.
-- If several givens match, the first one wins (same policy as the
-- exact match in solveMany; duplicates typically come from
-- superclass diamonds).
matchFlexGoal :: SLoc -> EConstraint -> [(Ident, EConstraint)] -> Maybe (Ident, [Improve])
matchFlexGoal loc ct ads =
  case [ (ai, mkImp s)
       | (ai, act) <- ads
       , let (wh, was) = splitApp ct
             (gh, gas) = splitApp act
       , length was == length gas
       , Just (s, _) <- [matchTypes loc (wh : was) (gh : gas) []]
       ] of
    (ai, is) : _ -> Just (ai, is)
    _            -> Nothing
  where mkImp s = [ (loc, EUVar i, t) | (i, t) <- s ]

-- Split a type application into head and arguments, mirroring getAppM
-- but keeping a flexible head instead of failing on it.
splitApp :: EType -> (EType, [EType])
splitApp = loop []
  where loop as (EApp f a) = loop (a : as) f
        loop as (EParen e) = loop as e
        loop as (EOper e1 [(op, e2)]) = loop as $ EApp (EApp (EVar op) e1) e2
        loop as t = (t, as)

solveInst :: SolveOne
solveInst loc iCls cts = do
--  traceM $ "solveInst " ++ prettyShow cts
  it <- gets instTable
--  tcTrace ("instances:\n" ++ unlines (map showInstDef (M.toList it)))
  -- XXX The solveGen&co functions are not in the T monad.
  -- But we sometimes need to instantiate type variable, so we use the
  -- hack to pass dowwn a starting uniq.
  -- This ought to be fixed, but is will be less efficient.
  uniq <- do ts <- get; let { u = unique ts }; put ts{ unique = u+100 }; return u   -- make room for many UVars
  case M.lookup iCls it of
    Nothing -> return Nothing   -- no instances, so no chance
    Just (InstInfo atomMap insts fds) -> do
--      tcTrace $ "solveInst: " ++ showIdent iCls ++ " atomMap size=" ++ show (M.size atomMap)
      case cts of
        [EVar i] -> do
          case M.lookup i atomMap of
            -- If the goal is just (C T) and there is an instance, the solution is simple
            Just e  -> return $ Just (e, [], [])
            -- Not found, but there might be a generic instance
            Nothing -> solveGen uniq (M.null atomMap) fds insts loc iCls cts
        _           -> solveGen uniq (M.null atomMap) fds insts loc iCls cts

-- When matching constraint (C _a) against an instance of the form
-- instance (C b) then we don't want to match if the
-- _a is later instantiated and it turns out we should
-- have matched a (C T) instead.
solveGen :: TRef -> Bool -> [IFunDep] -> [InstDict] -> SolveOne
solveGen uniq noAtoms fds insts loc iCls cts = do
--  tcTrace ("solveGen: " ++ show (iCls, cts))
--  tcTrace ("solveGen: insts=" ++ show insts)
  eqs <- gets typeEqTable
  feqs <- gets famEqTable
  syns <- gets synTable
  let isDictArgE (EVar i)   = (adictPrefix ++ uniqIdentSep) `isPrefixOf` unIdent i
      isDictArgE (EApp f a) = isDictArgE f || isDictArgE a
      isDictArgE _          = False
      normLocal t = normTypeEq eqs (expandSynFull syns feqs (normTypeEq eqs t))
      normInst d@(InstDict de ctxts)
        | (not (null eqs) || not (null feqs)) && isDictArgE de =
            InstDict de (\u -> let (ctx, ts) = ctxts u in (map normLocal ctx, map normLocal ts))
        | otherwise = d
      matches = getBestMatches $ findMatches uniq noAtoms loc fds (map normInst insts) cts
--  tcTrace ("solveGen: matches allMatches =" ++ showListS show (findMatches uniq noAtoms loc fds insts cts))
--  tcTrace ("solveGen: matches bestMatches=" ++ showListS showMatch matches)
  case matches of
    []              -> return Nothing
    [(de, ctx, is)] ->
      if null ctx then
        return $ Just (de, [], is)
      else do
        d <- newDictIdent loc
--        tcTrace ("constraint " ++ showIdent di ++ " :: " ++ showEType ct ++ "\n" ++
--                "   turns into " ++ showIdent d ++ " :: " ++ showEType (tupleConstraints ctx) ++ ", " ++
--                showIdent di ++ " = " ++ showExpr (EApp de (EVar d)))
        return $ Just (EApp de (EVar d), [(d, tupleConstraints ctx)], is)
    _ -> tcError loc $ "Multiple constraint solutions for: " ++ showEType (tApps iCls cts)
--                     ++ show (map fst matches)

-- Split a tupled contraint into its parts.
-- XXX should look for a direct (tupled) dictionary
solveTuple :: SolveOne
solveTuple loc _iCls cts = do
--  traceM $ "solveTuple " ++ prettyShow cts
  goals <- mapM (\ c -> do { d <- newDictIdent loc; return (d, c) }) cts
  return $ Just (ETuple (map (EVar . fst) goals), goals, [])

solveTypeEq :: SolveOne
-- If either type is a unification variable, just do the unification.
solveTypeEq loc _iCls [t1, t2] | isEUVar t1 || isEUVar t2 = return $ Just (ETuple [], [], [(loc, t1, t2)])
                               | otherwise = do
--  traceM $ "solveTypeEq " ++ prettyShow [t1, t2]
  syns <- gets synTable
  -- Never split an equality headed by a stuck type family into subgoals:
  -- F a ~ G b must not become F ~ G and a ~ b.  Identical stuck
  -- applications are discharged by solveEq's normalization check and
  -- same-headed ones split soundly below; anything else stays unsolved
  -- so given family equalities (famEqTable) can discharge it later.
  t1e <- normConstraint t1
  t2e <- normConstraint t2
  let sameHead = case (appHeadIdent t1e, appHeadIdent t2e) of
                   (Just h1, Just h2) -> h1 == h2
                   _                  -> False
  if (famHeaded syns t1e || famHeaded syns t2e) && not sameHead then do
    if t1e `eqEType` t2e
      then return $ Just (ETuple [], [], [])
      else do
        mimps <- tryFamInjImprove loc syns t1e t2e
        case mimps of
          Nothing -> return Nothing
          Just imps -> do
            -- Re-verify the full equality after the improvement unifies
            -- the meta variable(s).
            d' <- newDictIdent loc
            return $ Just (ETuple [], [(d', mkEqType loc t1e t2e)], imps)
  else do
      eqs <- gets typeEqTable
      --tcTrace ("solveTypeEq eqs=" ++ show eqs)
      case solveEq eqs t1e t2e of
        Nothing -> return Nothing
        Just tts -> do
          let mkEq (u1, u2) = do
                i <- newDictIdent loc
                return (i, mkEqType loc u1 u2)
          ncs <- mapM mkEq tts
          return $ Just (ETuple [], ncs, [])
solveTypeEq _ _ _ = impossible

-- Injectivity improvement for type families declared with
-- @type family F a ... = r | r -> ...@: when a stuck family application
-- @F args@ is equated with a non-family type, the result variable @r@
-- determines the annotated arguments, so matching the other side against
-- every equation's RHS can pin down an injective argument.
-- Every candidate equation that is not definitely apart must agree on the
-- improved argument; the full equality is re-checked after unification,
-- so this is sound and terminates (a meta variable is always refined).
tryFamInjImprove :: SLoc -> SynTable -> EType -> EType -> T (Maybe [Improve])
tryFamInjImprove loc syns t1e t2e = do
  imps1 <- tryPair t1e t2e
  if not (null imps1) then return (Just imps1) else do
    imps2 <- tryPair t2e t1e
    return (if null imps2 then Nothing else Just imps2)
  where tryPair famSide otherSide =
          case getAppM famSide of
            Nothing -> return []
            Just (h, allArgs) ->
              case M.lookup h syns >>= unTFamEntry of
                Nothing -> return []
                Just (_, arity, inj, eqns)
                  | not (or inj) -> return []
                  | length allArgs /= arity -> return []
                  | null eqns -> return []
                  | famHeaded syns otherSide -> return []
                  | isEUVar otherSide -> return []
                  | otherwise -> do
                      feqs <- gets famEqTable
                      let otherExp = expandSynFull syns feqs otherSide
                          cands = [ (pvs, pats, sub)
                                  | (pvs, pats, rhs) <- eqns
                                  , length pats == arity
                                  , let rhsExp = expandSynFull syns feqs rhs
                                  , Just sub <- [matchInjRHS syns pvs rhsExp otherExp] ]
                      if null cands then return [] else
                        fmap concat $ forM (zip3 inj allArgs [0..]) $ \ (idxIsInj, famArg, k) ->
                          if not idxIsInj || null (metaTvs [famArg]) then return [] else do
                            let mtgts = [ if all (`elem` map fst sub) (freeTyVars [pats !! k] `intersect` pvs)
                                          then Just (subst sub (pats !! k))
                                          else Nothing
                                        | (pvs, pats, sub) <- cands ]
                            case sequence mtgts of
                              Nothing -> return []
                              Just [] -> return []
                              Just (t0 : ts)
                                | all (eqEType t0) ts
                                , not (famArg `eqEType` t0) -> return [(loc, famArg, t0)]
                                | otherwise -> return []

-- Match an injective family's equation RHS against the other side of an
-- equality, collecting bindings for the equation's pattern variables.
-- Returns Nothing only when the two types are definitely apart, so a
-- genuine reduction of the family application is never discarded:
-- family applications and unification variables on either side block
-- (Just []), as do non-clashing rigid variables and constructors.
matchInjRHS :: SynTable -> [Ident] -> EType -> EType -> Maybe [(Ident, EType)]
matchInjRHS syns pvs pat arg =
  case (strip pat, strip arg) of
    (EVar v, a) | v `elem` pvs -> Just [(v, a)]
    (p, a) | famHeaded syns p -> Just []
           | famHeaded syns a -> Just []
           | isEUVar a -> Just []
    (EVar c1, EVar c2) -> if c1 == c2 then Just [] else Nothing
    (ELit _ l1, ELit _ l2) -> if l1 == l2 then Just [] else Nothing
    (p, a) ->
      case (getAppM p, getAppM a) of
        (Just (c1, as1), Just (c2, as2))
          | isRigidConHead syns c1, isRigidConHead syns c2 ->
              if c1 /= c2 || length as1 /= length as2 then Nothing
              else combineSubs (zipWith (matchInjRHS syns pvs) as1 as2)
        _ ->
          case (p, a) of
            (EApp f1 x1, EApp f2 x2) ->
              combineSubs [matchInjRHS syns pvs f1 f2, matchInjRHS syns pvs x1 x2]
            _ | (isRigidCon p && isLit a) || (isLit p && isRigidCon a) -> Nothing
              | otherwise -> Just []
  where strip (EParen t) = strip t
        strip (ESign t _) = strip t
        strip t = t
        isRigidCon t = case getAppM t of
                         Just (c, _) -> isRigidConHead syns c
                         Nothing -> False
        isLit (ELit _ _) = True
        isLit _ = False
        combineSubs = foldr combine (Just [])
          where combine _ Nothing = Nothing
                combine Nothing _ = Nothing
                combine (Just s1) (Just s2) = foldr ins (Just s1) s2
                ins _ Nothing = Nothing
                ins (v, t) (Just acc) =
                  case lookup v acc of
                    Nothing -> Just ((v, t) : acc)
                    Just t' | t `eqEType` t' -> Just acc
                            | otherwise -> Nothing

solveCoercible :: HasCallStack => SolveOne
solveCoercible loc iCls [t1, t2] = do
--  traceM $ "solveCoercible " ++ prettyShow [t1, t2]
  syns <- gets synTable
  dt <- gets dataTable
  t1s <- normConstraint t1
  t2s <- normConstraint t2
  let mkGoal isEq u1 u2 = do
        i <- newDictIdent loc
        return (i, if isEq then mkEqType loc u1 u2 else mkCoercible loc u1 u2)
      isNewtypeCon qi = case M.lookup qi dt of
                          Just (Newtype _ _ _) -> True
                          _                    -> False
  if eqEType t1s t2s then
    return $ Just (ETuple [], [], [])
  else case (getAppM t1s, getAppM t2s) of
    (Just (h1, args1), Just (h2, args2))
      | h1 == h2, length args1 == length args2, not (isFamCon syns h1), not (null args1) ->
        if isNewtypeCon h1 then
          case (unwrapTopNewtype dt t1s, unwrapTopNewtype dt t2s) of
            (Just u1, Just u2) -> do
              nc <- mkGoal False u1 u2
              return $ Just (ETuple [], [nc], [])
            _ -> do
              ncs <- sequence (zipWith (mkGoal False) args1 args2)
              return $ Just (ETuple [], ncs, [])
        else do
          let base = unIdent (unQualIdent h1)
              argRoles
                | base == "Set"     && length args1 == 1 = [True]
                | base == "HashSet" && length args1 == 1 = [True]
                | base == "Map"     && length args1 == 2 = [True, False]
                | base == "HashMap" && length args1 == 2 = [True, False]
                | otherwise                              = replicate (length args1) False
          ncs <- sequence (zipWith3 mkGoal argRoles args1 args2)
          return $ Just (ETuple [], ncs, [])
    _ | not (isEUVar t1s || isEUVar t2s)
      , Just u1 <- unwrapTopNewtype dt t1s -> do
          nc <- mkGoal False u1 t2s
          return $ Just (ETuple [], [nc], [])
      | not (isEUVar t1s || isEUVar t2s)
      , Just u2 <- unwrapTopNewtype dt t2s -> do
          nc <- mkGoal False t1s u2
          return $ Just (ETuple [], [nc], [])
      | otherwise -> do
          -- pretend newtypes are type synonyms
          (t1', t2') <- withNewtypeAsSyns $
            (,) <$> expandSynNoChk t1s <*> expandSynNoChk t2s
          case genCoerce t1' t2' of
            Nothing -> solveInstCoercible loc iCls t1 t2  -- look for a dict argument
            Just [(u1, u2)] | isEUVar u1 || isEUVar u2 || (u1 `eqEType` t1s && u2 `eqEType` t2s) ->
              solveInstCoercible loc iCls t1 t2  -- look for a dict argument
            Just tts -> do
              ncs <- mapM (uncurry (mkGoal False)) tts
              return $ Just (ETuple [], ncs, [])
solveCoercible _ _ _ = impossible

unwrapTopNewtype :: DataTable -> EType -> Maybe EType
unwrapTopNewtype dt t
  | Just (qi, args) <- getAppM t
  , Just (Newtype (_, vs) (Constr _ _ _ _ et) _) <- M.lookup qi dt
  , let n = length vs
  , length args >= n
  , let rhs = either (snd . head) (snd . snd . head) et
  , qi `notElem` allVarsExpr rhs
  , let (args1, argsRest) = splitAt n args
  = Just $ foldl EApp (subst (zip (map idKindIdent vs) args1) rhs) argsRest
  | otherwise = Nothing

genCoerce :: EType -> EType -> Maybe [(EType, EType)]
genCoerce t1 t2 | eqEType t1 t2 = Just []
genCoerce t1@(EUVar _) t2 = Just [(t1, t2)]
genCoerce t1@(EVar _)  t2 = Just [(t1, t2)]
genCoerce t1 t2@(EUVar _) = Just [(t1, t2)]
genCoerce t1 t2@(EVar _)  = Just [(t1, t2)]
genCoerce (EApp f1 a1) (EApp f2 a2) = (++) <$> genCoerce f1 f2 <*> genCoerce a1 a2
genCoerce _ _ = Nothing

solveInstCoercible :: SLoc -> Ident -> EType -> EType -> T (Maybe (Expr, [Goal], [Improve]))
solveInstCoercible loc iCls t1 t2 = do
{- XXX Should use the reflexive, symmetric, transitive closure for Coercible.
   XXX It's enough to do the transitive part for anything involving type variable.
   XXX See Data.Type.Coercion.trans for a failing example.
  it <- gets instTable
  case M.lookup iCls it of
    Nothing -> pure ()
    Just (InstInfo _ ds _) -> traceM ("solveInstCoercible: " ++ show [ f 0 | (_, f) <- ds ])
-}

  msol <- solveInst loc iCls [t1, t2]
  case msol of
    Nothing -> solveInst loc iCls [t2, t1]
    Just _ -> pure msol

-- Pretend newtypes are type synonyms.
-- XXX It's rather inefficient to do this over and over.
-- XXX We give up on direct recursive newtypes.  Should do it for mutual recursion too.
withNewtypeAsSyns :: T a -> T a
withNewtypeAsSyns act = do
  st <- gets synTable  -- get old syntable
  -- Copy newtypes to syn table
  dt <- gets dataTable
  let ext (qi, Newtype (_, vs) (Constr _ _ _c _ et) _) = do
          -- XXX We should check that the constructor name (_c) is visible.
          -- But this is tricky since we don't know under what qualified name it
          -- it could be visible.
          let t = either (snd . head) (snd . snd . head) et
--          traceM $ "extNewtypeSyns: " ++ showIdent qi ++ show vs ++ " = " ++ showExprRaw t
          unless (qi `elem` allVarsExpr t) $
            -- Not directly recursive
            extSyn qi vs t  -- extend synonym table
      ext _ = return ()
  mapM_ ext $ M.toList dt

  a <- act
  putSynTable st  -- put back old syntable
  pure a

isEUVar :: EType -> Bool
isEUVar (EUVar _) = True
isEUVar _ = False

solveKnownNat :: SolveOne
--solveKnownNat _ _ x | trace ("solveKnownNat: " ++ prettyShow x) False = undefined
solveKnownNat loc iCls [e@(ELit _ (LInteger _))] = mkConstDict loc iCls e
solveKnownNat loc iCls ts = solveInst loc iCls ts  -- look for a dict argument

solveKnownSymbol :: SolveOne
--solveKnownSymbol _ _ x | trace ("solveKnownSymbol: " ++ prettyShow x) False = undefined
solveKnownSymbol loc iCls [e@(ELit _ (LStr _))] = mkConstDict loc iCls e
solveKnownSymbol loc iCls ts = solveInst loc iCls ts  -- look for a dict argument

solveTypeable :: SolveOne
solveTypeable loc iCls ts@[t] = do
  msol <- solveInst loc iCls ts
  case msol of
    Just _ -> return msol
    Nothing -> do
      let mkTr mdl nam =
            Just ( EApp (EVar (mkClassConstructor iCls))
                        (EApp (EApp (EVar (mkIdentB "Data.Typeable._mkTyCon")) mdl) nam)
                 , [], [] )
          litStr = ELit loc . LStr
      case t of
        ELit _ (LStr s)     -> return $ mkTr (litStr "Data.TypeLits") (litStr (show s))
        ELit _ (LInteger n) -> return $ mkTr (litStr "Data.TypeLits") (litStr (show n))
        EVar p | isPromotedIdent p -> return $ mkTr (litStr "DataKinds") (litStr (unIdent p))
        EVar _ -> do
          mks <- solveKnownSymbol loc (mkIdent nameKnownSymbol) [t]
          case mks of
            Just (ksDict, gs, imps) -> do
              let symStr = EApp (EApp (EVar (mkIdentB "Data.TypeLits.symbolVal")) ksDict)
                                (ELit loc (LInt 0))
              return $ Just ( EApp (EVar (mkClassConstructor iCls))
                                   (EApp (EApp (EVar (mkIdentB "Data.Typeable._mkTyCon")) (litStr "Data.TypeLits")) symStr)
                            , gs, imps )
            Nothing -> do
              mkn <- solveKnownNat loc (mkIdent nameKnownNat) [t]
              case mkn of
                Just (knDict, gs, imps) -> do
                  let natValExpr = EApp (EApp (EVar (mkIdentB "Data.TypeLits.natVal")) knDict)
                                        (ELit loc (LInt 0))
                      natStr = EApp (EVar (mkIdentB "Data.Integer.Internal.showInteger")) natValExpr
                  return $ Just ( EApp (EVar (mkClassConstructor iCls))
                                       (EApp (EApp (EVar (mkIdentB "Data.Typeable._mkTyCon")) (litStr "Data.TypeLits")) natStr)
                                , gs, imps )
                Nothing -> return Nothing
        _ -> return Nothing
solveTypeable loc iCls ts = solveInst loc iCls ts

mkConstDict :: SLoc -> Ident -> Expr -> T (Maybe (Expr, [Goal], [Improve]))
mkConstDict loc iCls e = do
  let res = EApp (EVar $ mkClassConstructor iCls) fcn
      fcn = EApp (ELit loc (LPrim "K")) e                -- constant function
  return $ Just (res, [], [])

type TySubst = [(TRef, EType)]

-- Given some instances and a constraint, find the matching instances.
-- For each matching instance return: (subst-size, (dict-expression, new-constraints))
-- The subst-size is the size of the substitution that made the input instance match.
-- It is a measure of how exact the match is.
findMatches :: TRef -> Bool -> SLoc -> [IFunDep] -> [InstDict] -> [EType] -> [(Int, (Expr, [EConstraint], [Improve]))]
findMatches _ False _ _ _ [EUVar _] = []
findMatches uniq _ loc fds ds its =
 let rrr =
       [ (length s, (de, map (substEUVar s) ctx, imp))
       | (InstDict de ctxts) <- ds
       , let (ctx, ts) = ctxts uniq
       , Just (s, imp) <- [matchTypes loc ts its fds]
       ]
 in --trace ("findMatches: " ++ showListS showInstDict ds ++ "; " ++ show its ++ "; " ++ show fds ++ "; " ++ show rrr)
    rrr

-- Do substitution for EUVar.
-- XXX similar to derefUVar
substEUVar :: TySubst -> EType -> EType
substEUVar [] t = t
substEUVar _ t@(EVar _) = t
substEUVar _ t@(ELit _ _) = t
substEUVar s (EApp f a) = EApp (substEUVar s f) (substEUVar s a)
substEUVar s t@(EUVar i) = fromMaybe t $ lookup i s
substEUVar s (EForall b iks t) = EForall b iks (substEUVar s t)
substEUVar _ _ = impossible

-- Length of lists match, because of kind correctness.
-- fds is a non-empty list.
matchTypes :: SLoc -> [EType] -> [EType] -> [IFunDep] -> Maybe (TySubst, [Improve])
matchTypes _ ats ats' [] = do
  -- Simple special case when there are no fundeps.
--  traceM $ "\nmatchTypes " ++ prettyShow (ats, ats') ++ show ats
  let loop r (t:ts) (t':ts') = matchType r t t' >>= \ r' -> loop r' ts ts'
      loop r _ _ = pure r
  s <- loop [] ats ats'
--  traceM $ "\nmatchTypes " ++ prettyShow (ats, ats', s)
  pure (s, [])
matchTypes loc ts ts' fds = asum $ map (matchTypesFD loc ts ts') fds

matchTypesFD :: SLoc -> [EType] -> [EType] -> IFunDep -> Maybe (TySubst, [Improve])
--matchTypesFD _ ts ts' io | trace ("matchTypesFD: " ++ show (ts, ts', io)) False = undefined
matchTypesFD loc ts ts' (ins, outs) = do
  let matchFD :: Bool -> EType -> EType -> Maybe TySubst
      matchFD True  = \ _ _ -> Just []     -- if it's an output, don't match
      matchFD False = matchType []          -- match types for non-outputs
  tms <- sequence $ zipWith3 matchFD outs ts ts'
  tm  <- combineTySubsts tms               -- combine all substitutions
  is  <- combineTySubsts [ s | (True, s) <- zip ins tms]  -- subst from input FDs
  let imp = [ (loc, substEUVar is t, t') | (True, t, t') <- zip3 outs ts ts' ]  -- improvements
  pure (tm, imp)

-- Match two types, instantiate variables in the first type.
matchType :: TySubst -> EType -> EType -> Maybe TySubst
matchType = match
  where
    match r (EVar i)   (EVar i')   | i == i' = pure r
    match r (ELit _ l) (ELit _ l') | l == l' = pure r
    match r (EApp f a) (EApp f' a') = do
      r' <- match r f f'
      match r' a a'
--    match _ _ (EUVar _) = Nothing
    match r (EUVar i) t' =
      -- For a variable, check that any previous match is the same.
      case lookup i r of
        Just t  -> match r t t'
        Nothing -> pure ((i, t') : r)
    match _ _ _ = Nothing

-- XXX This shouldn't be this complicated.
combineTySubsts :: [TySubst] -> Maybe TySubst
combineTySubsts = combs []
  where
    combs r [] = Just r
    combs r (s:ss) = do { r' <- comb r s; combs r' ss }
    comb :: TySubst -> TySubst -> Maybe TySubst
    comb r [] = Just r
    comb r ((v, t):s) = do { r' <- comb1 v t r; comb r' s }
    comb1 v t r =
      case lookup v r of
        Nothing -> Just ((v, t) : r)
        Just t' -> matchType r t' t

-- Get the best matches.  These are the matches with the smallest substitution.
-- Always prefer arguments rather than global instances.
-- If there are multiple alternatives with the args, just pick one.
-- This can arise from diamonds in the superclass chain.
getBestMatches :: [(Int, (Expr, [EConstraint], [Improve]))] -> [(Expr, [EConstraint], [Improve])]
getBestMatches [] = []
getBestMatches ams =
  let isDictArg (EVar i) = (adictPrefix ++ uniqIdentSep) `isPrefixOf` unIdent i
      isDictArg _ = True
      (args, insts) = partition (\ (_, (ei, _, _)) -> isDictArg ei) ams
      pick ms =
        let b = minimum (map fst ms)         -- minimum substitution size
        in  [ ec | (s, ec) <- ms, s == b ]   -- pick out the smallest
  in  if null args then pick insts else take 1 (pick args)

-- Check that there are no unsolved constraints.
checkConstraints :: HasCallStack => T ()
checkConstraints = do
  cs <- gets constraints
  case cs of
    [] -> modify $ \ ts -> ts { impEqTable = M.empty }
    (i, t) : _ -> do
      t' <- derefUVar t
      case t' of
        EApp (EApp (EVar eq) a) e | eq == identTypeEq -> mismatchError (getSLoc i) (a, e)
        _ -> do
          c <- head <$> niceTypes [t']
          tcError (getSLoc i) $ "no instance for (" ++ showTypeUser c ++ ")"
{-
      is <- gets instTable
      traceM $ "Cannot satisfy constraint: " ++ unlines (map (\ (xi, ii) -> show xi ++ ":\n  " ++ showInstInfo ii) (M.toList is))
      let EApp (EVar xi) _ = t'
          Just ii = M.lookup xi is
      traceM ("lookup " ++ showInstInfo ii)
      solveConstraints
      cs' <- gets constraints
      traceM (show (length cs, length cs'))
-}

-- Add a type equality constraint.
addEqConstraint :: SLoc -> EType -> EType -> T ()
addEqConstraint loc t1 t2 = do
  d <- newDictIdent loc
  addConstraint d (mkEqType loc t1 t2)

-- Possibly solve a type equality.
-- Just normalize both types and compare.
solveEq :: TypeEqTable -> EType -> EType -> Maybe [(EType, EType)]
--solveEq eqs t1 t2 | trace ("solveEq: " ++ show (t1,t2) ++ show eqs) False = undefined
solveEq eqs t1 t2 | normTypeEq eqs t1 `eqEType` normTypeEq eqs t2 = Just []
                  | otherwise =
  case (t1, t2) of
    (EApp f1 a1, EApp f2 a2) -> Just [(f1, f2), (a1, a2)]
    _                        -> Nothing

-- Add the equality t1~t2.
-- Type equalities are saved as a rewrite system where all the rules
-- have the form
--   v -> rhs
-- where v is a type variable (rigid or skolem), and the rhs contains
-- only type constructors and type variables that are not the LHS of any rule.
-- To find out if two types are equal according to the known equalites,
-- we just normalize both type using the rewrite rules (which is just a substitution).
-- When we get TypeFamilies the LHS has to be a type expression as well.
-- And then rewrite rules can probably be obtained with Knuth-Bendix completion
-- of the equalities.
-- Note: there should be no meta variables in t1 and t2.
-- XXX This guaranteed by how it's called, but I'm not sure it always works properly.
addTypeEq :: SynTable -> EType -> EType -> TypeEqTable -> TypeEqTable
addTypeEq syns t1 t2 aeqs =
  let deref (EVar i) | Just t <- lookup i aeqs = t
      deref (ESign t _) = t
      deref t = t
      t1' = deref t1
      t2' = deref t2
      isVar = not . isConIdent
      addEq i t its = (i, t) : map (second $ subst [(i, t)]) its
      -- Heads of a stuck family application must never be split apart:
      -- F a ~ G b (or F a ~ Maybe b) cannot be decomposed, and the
      -- variable-headed TypeEqTable cannot represent it either, so the
      -- equation is left unrecorded here (addEqDict records top-level
      -- stuck applications in the famEqTable instead).
      stuckHeads = case (appHeadIdent t1', appHeadIdent t2') of
                     (Just h1, Just h2) | h1 /= h2 -> isFamCon syns h1 || isFamCon syns h2
                     _ -> False
{-
      chkTypeEqs :: TypeEqTable -> TypeEqTable
      chkTypeEqs xeqs =
        let rhsVars = nub $ filter isVar $ concatMap (allVarsExpr . snd) xeqs
            lhsVars = map fst xeqs
        in  if null (intersect lhsVars rhsVars) then xeqs
            else error $ "addTypeEq: " ++ show ((t1, t1'), (t2, t2'), (lhsVars, rhsVars), xeqs, aeqs)
-}
  in  -- chkTypeEqs $
      case (t1', t2') of
        (EVar i1, EVar i2) | isVar i1 && isVar i2 ->
               if i1 < i2 then addEq i2 t1' aeqs  -- always point smaller to bigger
          else if i1 > i2 then addEq i1 t2' aeqs
          else                             aeqs
        (EVar i1, _) | isVar i1, i1 `notElem` allVarsExpr t2' -> addEq i1 t2' aeqs
        (_, EVar i2) | isVar i2, i2 `notElem` allVarsExpr t1' -> addEq i2 t1' aeqs
        (EVar i1, _) | isVar i1 -> aeqs
        (_, EVar i2) | isVar i2 -> aeqs
        (EApp f1 a1, EApp f2 a2) | not stuckHeads -> addTypeEq syns f1 f2 (addTypeEq syns a1 a2 aeqs)
        _ | t1' `eqEType` t2 -> aeqs
        _ | stuckHeads -> aeqs  -- stuck family application: cannot split or represent; keep silent
        _ -> errorMessage (getSLoc t1) $ "inconsistent type equality " ++ showEType t1' ++ " ~ " ++ showEType t2'

-- Normalize a type with the known type equalties.
-- For now, it's just substitution.
normTypeEq :: TypeEqTable -> EType -> EType
normTypeEq = subst

---------------------

-- Try adding all dictionaries that used to have meta variables.
addMetaDicts :: T ()
addMetaDicts = do
  ms <- gets metaTable
  putMetaTable []
  mapM_ addDict ms  -- Try adding them

-----------------------------

showValueExport :: ValueExport -> String
showValueExport (ValueExport i (Entry qi t)) =
  showIdent i ++ " = " ++ showExprRaw qi ++ " :: " ++ showEType t

showTypeExport :: TypeExport -> String
showTypeExport (TypeExport i (Entry qi t) _) =
  showIdent i ++ " = " ++ showExprRaw qi ++ " :: " ++ showEType t
    -- ++ " assoc=" ++ showListS showValueExport vs

showTypeExportAssocs :: TypeExport -> [String]
showTypeExportAssocs (TypeExport _ _ vs) = map showValueExport vs

{-
showSymTab :: SymTab -> String
showSymTab (SymTab im ies) = showListS showIdent (map fst (M.toList im) ++ map fst ies)

showTModuleExps :: TModule a -> String
showTModuleExps (TModule mn _fxs tys _syns _clss _insts vals _defs) =
  showIdent mn ++ ":\n" ++
    unlines (map (("  " ++) . showValueExport) vals) ++
    unlines (map (("  " ++) . showTypeExport)  tys)

showIdentClassInfo :: (Ident, ClassInfo) -> String
showIdentClassInfo (i, (_vks, _ctx, cc, ms)) =
  showIdent i ++ " :: " ++ showEType cc ++
    " has " ++ showListS showIdent ms
-}

doDeriving :: EDef -> T [EDef]
doDeriving def@(Data    lhs cs ds)    = (def:) . concat <$> mapM (deriveDer False lhs  cs) (addTypeable (getSLoc lhs) ds)
doDeriving def@(Newtype lhs  c ds)    = (def:) . concat <$> mapM (deriveDer True  lhs [c]) (addTypeable (getSLoc lhs) ds)
doDeriving (StandDeriving as _ act)   = do
  -- The StandDeriving has not been typechecked yet, so do it now.
  def@(StandDeriving s n ct) <- withTypeTable $ tcStand as act
  (def:) <$> standaloneDeriving s n ct
doDeriving def@(Class _ (n, _) _ _) | unIdent n /= "~" && deriveClassTypeable = do  -- "~" is a special class, don't touch it
  -- classes need to be Typeable
  mn <- gets moduleName
  return [def, mkTypeableInst mn n]
doDeriving def                        = return [def]

-- Add Data.Typeable to the derivings.
-- Also skip all derivings (including Typeable) if it is says 'deriving ()'
addTypeable :: SLoc -> [Deriving] -> [Deriving]
addTypeable _ dss | doNotDerive dss = []
addTypeable loc dss = Deriving DerNone [(0, EVar $ mkIdentSLoc loc nameDataTypeableTypeable)] : map (\ (Deriving strat ds) -> Deriving strat (filter (not . isDT) ds)) dss
  where isDT (_, EVar dt) = dt == identDataTypeableTypeable
        isDT _ = False

deriveDer :: Bool -> LHS -> [Constr] -> Deriving -> T [EDef]
deriveDer newt lhs cs (Deriving strat ds) = concat <$> mapM (deriveStrat Nothing newt lhs cs strat) ds

standaloneDeriving :: DerStrategy -> Int -> EConstraint -> T [EDef]
standaloneDeriving str narg act = do
  let (_vks, _ctx, cc) = splitContext act
--  traceM ("standaloneDeriving 1 " ++ show (_vks, _ctx, cc))
  (cls, ts, tname) <-
    case getAppM cc of
      Just (c, ts@(_:_)) | Just (n, _) <- getAppM (last ts) -> return (c, init ts, n)
      _ -> tcError (getSLoc act) "malformed standalone deriving"
--  traceM ("standaloneDeriving 2 " ++ show (act, cls, tname))
  dtable <- gets dataTable
  (lhs, newt, cs) <-
    case M.lookup tname dtable of
      Just (Newtype l  c _) -> return (l, True,  [c])
      Just (Data    l xs _) -> return (l, False, xs)
      _ -> tcError (getSLoc act) ("not data/newtype " ++ showIdent tname)
  -- We want 'instance ctx => cls ty'
  deriveStrat (Just (act, tname)) newt lhs cs str (narg, tApps cls ts)
