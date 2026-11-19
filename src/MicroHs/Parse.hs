-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns -Wno-unused-do-bind #-}
module MicroHs.Parse(P, pTop, pTopModule, parseDie, parse, pExprTop, keywords, dotDotIdent) where
import qualified Prelude(); import MHSPrelude hiding ((*>), (<*))
import Control.Applicative hiding ((*>), (<*))
import Control.Monad
import Control.Monad.Fail
import Data.Char
import Data.Either
import Data.List
import Data.Maybe
import Text.ParserComb as P
import MicroHs.Builtin(builtinMdl)
--import MicroHs.Error(MhsError(MhsSyntaxError))
import MicroHs.Lex
import MicroHs.List
import MicroHs.Expr hiding (getSLoc)
import qualified MicroHs.Expr as E
import MicroHs.Ident
import Text.PrettyPrint.HughesPJLiteClass(prettyShow)
--import Debug.Trace

-- Hugs can't define the efficient *>
infixl 4 *>, <*
(*>) :: Prsr s t a -> Prsr s t b -> Prsr s t b
(*>) = (>>)

-- Slightly faster than the <* from Applicative
(<*) :: Prsr s t a -> Prsr s t b -> Prsr s t a
(<*) = (<<)

type P a = Prsr LexState Token a

parseDie :: forall a . -- (Show a) =>
            P a -> FilePath -> String -> a
parseDie p fn file =
  case parse p fn file of
    Left err -> throw err
    Right a -> a

parse :: forall a . -- (Show a) =>
         P a -> FilePath -> String -> Either MhsError a
parse p fn file =
  let { ts = lexTopLS fn file } in
  case runPrsr p ts of
    Left lf -> Left $ formatFailed lf
    Right a -> Right a

guardM :: P a -> (a -> Bool) -> P a
guardM ma p = do a <- ma; guard (p a); pure a

getSLoc :: P SLoc
getSLoc = do
  t <- nextToken
  pure (tokensLoc [t])

eof :: P ()
eof = do
  t <- nextToken
  case t of
    TEnd _ -> pure ()
    _      -> Control.Monad.Fail.fail "eof"

comma, equal, bar, semi, lpar, rpar, lbra, rbra :: P ()
comma = pSpec ','
equal = pSpec '='
bar   = pSpec '|'
semi  = pSpec ';'
lpar  = pSpec '('
rpar  = pSpec ')'
lbra  = pSpec '['
rbra  = pSpec ']'

pTop :: P EModule
pTop = (pModule <|> pModuleEmpty) <* eof

pTopModule :: P EModule
pTopModule = pModule <* eof

pExprTop :: P Expr
pExprTop = pBraces pExpr <* eof

pModule :: P EModule
pModule = do
  pKeyword "module"
  mn <- pUQIdentA
  exps <- (lpar *> sepSEBy pExportItem comma <* rpar)
      <|> pure [ExpModule mn]
  pKeyword "where"
  defs <- pBlock pDef
  pure $ EModule mn exps defs

-- Optional leading and trailing
sepSEBy :: P a -> P b -> P [a]
sepSEBy p sep = (sep *> sepEndBy1 p sep) <|> sepEndBy p sep

-- Optional leading and trailing, non-empty
sepSEBy1 :: P a -> P b -> P [a]
sepSEBy1 p sep = (sep *> sepEndBy1 p sep) <|> sepEndBy1 p sep

pModuleEmpty :: P EModule
pModuleEmpty = do
  defs <- pBlock pDef
  --let loc = getSLoc defs
  pure $ EModule (mkIdent "Main") [ExpValue $ mkIdent "main"] defs

-- Possibly qualified alphanumeric identifier
pQIdent :: P Ident
pQIdent = do
  let
    is (TIdent loc qs s) | isAlpha_ (head s) = Just (qualName loc qs s)
    is _ = Nothing
  satisfyM "QIdent" is

-- Upper case, unqualified, alphanumeric identifier
-- (also accepts a DataKinds promotion tick, e.g. 'Con)
pUIdentA :: P Ident
pUIdentA = do
  let
    is (TIdent loc [] s) | isUpper (head s) = Just (mkIdentSLoc loc s)
                         | isTickCon s      = Just (mkIdentSLoc loc s)
    is _ = Nothing
  satisfyM "UIdent" is

-- Is s a promoted data constructor, i.e. '\'' followed by an uppercase name?
isTickCon :: String -> Bool
isTickCon ('\'':c:_) = isUpper c
isTickCon _          = False

-- Upper case, unqualified identifier
pUIdent :: P Ident
pUIdent =
      pUIdentA
  <|> pUIdentSpecial

-- Upper case, unqualified, identifier or symbol
pUIdentSym :: P Ident
pUIdentSym = pUIdent <|> pParens pUSymOper

-- Special "identifiers": [] (,) ...
pUIdentSpecial :: P Ident
pUIdentSpecial = do
  loc <- getSLoc
  let
    mk = mkIdentSLoc loc
  (mk . map (const ',') <$> (lpar *> some comma <* rpar))
    <|> (mk "[]" <$ (lbra *> rbra))  -- Allow [] as a constructor name

-- Upper case, possibly qualified, alphanumeric identifier
-- (also accepts a DataKinds promotion tick, e.g. 'Con, 'M.Con)
pUQIdentA :: P Ident
pUQIdentA = do
  let
    is (TIdent loc qs s) | isUpper (head s) = Just (qualName loc qs s)
                         | isTickCon s      = Just (qualName loc qs s)
    is _ = Nothing
  satisfyM "UQIdent" is

-- Upper case, possibly qualified, identifier
pUQIdent :: P Ident
pUQIdent =
      pUQIdentA
  <|> pUIdentSpecial

-- Lower case, unqualified identifier
pLIdent :: P Ident
pLIdent = do
  let
    is (TIdent loc [] s) | isLower_ (head s) && not (isKeyword s) = Just (mkIdentSLoc loc s)
    is _ = Nothing
  satisfyM "LIdent" is

-- Lower case, possibly qualified identifier
pLQIdent :: P Ident
pLQIdent = do
  let
    is (TIdent loc qs s) | isLower_ (head s) && not (isKeyword s) = Just (qualName loc qs s)
    is _ = Nothing
  satisfyM "LQIdent" is

-- Type names can be any operator
pTypeIdentSym :: P Ident
pTypeIdentSym = pUIdent <|> pParens pSymOper

-- A binary search for keywords saves about 1% compared to linear search.
{-
isKeyword s = elem s keywords
-}
isKeyword :: String -> Bool
isKeyword s =
  case compare s "in" of
    EQ -> True
    LT -> case compare s "deriving" of
            EQ -> True
            LT -> case compare s "class" of
                    EQ -> True
                    LT -> s == "_primitive" || s == "case"
                    GT -> s == "data" || s == "default"
            GT -> case compare s "forall" of
                    EQ -> True
                    LT -> s == "do" || s == "else"
                    GT -> s == "foreign" || s == "if" || s == "import"
    GT -> case compare s "newtype" of
            EQ -> True
            LT -> case compare s "infixr" of
                    EQ -> True
                    LT -> s == "infix" || s == "infixr"
                    GT -> s == "instance" || s == "let" || s == "mdo" || s == "module"
            GT -> case compare s "then" of
                    EQ -> True
                    LT -> s == "of" || s == "pattern"
                    GT -> s == "type" || s == "where"

keywords :: [String]
keywords =
  ["_primitive", "case", "class", "data", "default", "deriving", "do", "else", "forall", "foreign", "if",
   "import", "in", "infix", "infixl", "infixr", "instance",
   "let", "module", "newtype", "of", "pattern", "then", "type", "where"]

pSpec :: Char -> P ()
pSpec c = void (satisfy (showToken $ TSpec (SLoc "" 0 0) c) is)
  where
    is (TSpec _ d) = c == d
    is _ = False

pSymbol :: String -> P ()
pSymbol sym = void (satisfy sym is)
  where
    is (TIdent _ [] s) = s == sym
    is _ = False

pOper :: P Ident
pOper = pQSymOper <|> (pSpec '`' *> pQIdent <* pSpec '`')

pUOper :: P Ident
pUOper = pUQSymOper <|> (pSpec '`' *> pUQIdentA <* pSpec '`')

-- constructor operator
pConstrOper :: P Ident
pConstrOper = pUSymOper <|> (pSpec '`' *> pUIdentA <* pSpec '`')

pQSymOper :: P Ident
pQSymOper = do
  let
    is (TIdent loc qs s) | not (isAlpha_ (head s)) && s `notElem` reservedOps = Just (qualName loc qs s)
    is (TSpec  loc '!') = Just (mkIdentSLoc loc "!")
    is (TSpec  loc '~') = Just (mkIdentSLoc loc "~")
    is _ = Nothing
  satisfyM "QSymOper" is

pSymOper :: P Ident
pSymOper = do
  let
    is (TIdent loc [] s) | not (isAlpha_ (head s)) && s `notElem` reservedOps = Just (mkIdentSLoc loc s)
    is (TSpec  loc '!') = Just (mkIdentSLoc loc "!")
    is (TSpec  loc '~') = Just (mkIdentSLoc loc "~")
    is _ = Nothing
  satisfyM "SymOper" is

pUQSymOper :: P Ident
pUQSymOper = guardM pQSymOper isUOper

-- A constructor operator starts with ':' (or is a promoted operator like "':").
isUOper :: Ident -> Bool
isUOper i =
  case unIdent (unQualIdent i) of
    ':':_  -> True
    '\'':_ -> True
    _      -> False

pUSymOper :: P Ident
pUSymOper = guardM pSymOper isUOper

pLQSymOper :: P Ident
pLQSymOper = guardM pQSymOper (not . isUOper)

-- Allow -> as well
pLQSymOperArr :: P Ident
pLQSymOperArr = pLQSymOper <|> pQArrow

-- Parse ->, possibly qualified
pQArrow :: P Ident
pQArrow = do
  let
    is (TIdent loc qs s@"->") = Just (qualName loc qs s)
    is (TIdent loc qs s@"\x2192") = Just (qualName loc qs s)
    is _ = Nothing
  satisfyM "->" is

pLSymOper :: P Ident
pLSymOper = guardM pSymOper (not . isUOper)

reservedOps :: [String]
reservedOps = ["::", "<-", "..", "->", "=>",
               "\x2237", "\x2192", "\x21d2"] -- ::, -> and =>

pUQIdentSym :: P Ident
pUQIdentSym = pUQIdent <|> pParens pUQSymOper

-- Lower case, maybe qualified, identifier or symbol
pLQIdentSym :: P Ident
pLQIdentSym = pLQIdent <|> pParens pLQSymOperArr

-- Lower case, maybe qualified, symbol+arrow
pLQIdentSymbol :: P Ident
pLQIdentSymbol = pParens pLQSymOperArr

-- Lower case, unqualified, identifier or symbol
pLIdentSym :: P Ident
pLIdentSym = pLIdent <|> pParens pLSymOper

-- Lower case, unqualified, symbol
pLIdentSymbol :: P Ident
pLIdentSymbol = pParens pLSymOper

pParens :: forall a . P a -> P a
pParens p = lpar *> p <* rpar

-- Parse a qualifier used for literals
pLitQual :: P Ident
pLitQual = do
  let
    is (TQual l ss) = Just $ mkIdentSLoc l (intercalate "." ss)
    is _ = Nothing
  satisfyM "QualString" is

pLit :: P Expr
pLit = do
  mqual <- optional pLitQual
  let
    elit = maybe ELit (flip EQLit) mqual
    is (TString loc s) = Just (elit loc (LStr s))
    is (TBStr   loc s) = Just (elit loc (LBStr s))
    is (TChar   loc a) = Just (elit loc (LChar a))
    is (TInt    loc i) = Just (elit loc (LInteger i))
    is (TRat    loc d) = Just (elit loc (LRat d))
    is _ = Nothing
  satisfyM "literal" is <|> pInterpolate mqual

pInterpolate :: Maybe Ident -> P Expr
pInterpolate mqual = do
  -- XXX locations
  let mdl = fromMaybe builtinMdl mqual
      fin = EVar $ qualIdent mdl $ mkIdent "interpolateFinalize"
      raw = EVar $ qualIdent mdl $ mkIdent "interpolateRaw"
      val = EVar $ qualIdent mdl $ mkIdent "interpolateValue"
      app = EVar $ qualIdent mdl $ mkIdent "interpolateAppend"
      emp = EVar $ qualIdent mdl $ mkIdent "interpolateEmpty"
  let pStr = satisfyM "string" is
        where is (TString loc s) = Just $ EApp raw $ ELit loc (LStr s)
              is _ = Nothing
      pExp = pSpec '$' *> (EApp val <$> pExpr) <* pSpec '%'
  pSpec 'I'
  frags <- many (pStr <|> pExp)
  pSpec 'E'
  pure $ EApp fin $ foldr (eApp2 app) emp frags

pNumLit :: P Expr
pNumLit = guardM pLit isNum
  where isNum (ELit _ (LInteger _)) = True
        isNum (ELit _ (LRat _)) = True
        isNum _ = False

pString :: P String
pString = satisfyM "string" is
  where
    is (TString _ s) = Just s
    is _ = Nothing

---------------

pExportItem :: P ExportItem
pExportItem =
      ExpModule   <$> (pKeyword "module" *> pUQIdent)
  <|> ExpTypeSome <$> pUQIdentSym <*> pParens pConList
  <|> ExpTypeSome <$> pUQIdentSym <*> pure []
  <|> ExpValue    <$> pLQIdentSym
  <|> ExpValue    <$> (pKeyword "pattern" *> pUQIdentSym)
  <|> ExpTypeSome <$> (pKeyword "type" *> (pUQIdentSym <|> pLQIdentSymbol)) <*> (pParens pConList <|> pure [])
  <|> ExpDefault  <$> (pKeyword "default" *> (pUQIdentSym <|> pLQIdentSymbol))

pKeyword :: String -> P ()
pKeyword kw = void (satisfy kw is)
  where
    is (TIdent _ [] s) = kw == s
    is _ = False

pPragma :: String -> P ()
pPragma kw = void (satisfy kw is)
  where
    is (TPragma _ s) = kw == s
    is _ = False

pBraces :: forall a . P a -> P a
pBraces p =
  do
    pSpec '{'
    as <- p
    pSpec '}'
    pure as
 <|>
  do
    pSpec '<'          -- synthetic '{' (i.e., layout)
    as <- p
    -- If we are at a '>' token (i.e., synthetic '}') then
    -- all is well, if not then there is a parse error and we try
    -- recovering by popping they layout stack.
    -- This implements the Note 5 rule from Section 10.3 in
    -- the Haskell report.
    t <- nextToken
    case t of
      TSpec _ '>' -> pSpec '>'
      _           -> mapTokenState popLayout
    pure as

pBlock :: forall a . P a -> P [a]
pBlock p = pBraces body
  where body = optional semi *> sepBy p (some semi) <* optional semi


pDef :: P EDef
pDef =
      pBind        -- Fcn, Sign, PatBind, Infix
  <|> pTypeFamily
  <|> pTypeInstance
  <|> pDataFamily
  <|> pDataInstance
  <|> pNewtypeInstance
  <|> uncurry Data <$> (pKeyword "data"     *> pData) <*> pDerivings
  <|> Newtype      <$> (pKeyword "newtype"  *> pLHS) <*> (equal *> pField) <*> pDerivings
  <|> Type         <$> (pKeyword "type"     *> pLHS) <*> (equal *> pType)
  <|> Import       <$> (pKeyword "import"   *> pImportSpec)
  <|> ForImp       <$> (pKeyword "foreign"  *> pKeyword "import" *> pCallConv)
                        <*> (optional pSafety *> optional pString) <*> pLIdent <*> (dcolon *> pType)
  <|> ForExp       <$> (pKeyword "foreign"  *> pKeyword "export" *> pCallConv)
                        <*> optional pString <*> pFExpr <*> (dcolon *> pType)
  <|> Class        <$> (pKeyword "class"    *> pContext) <*> pLHS <*> pFunDeps     <*> pWhere pClsBind
  <|> Instance <$> (pKeyword "instance" *> pType) <*> pWhere pInstBind <*> (pWhere pInstBind <|> pure [])
  <|> Default      <$> (pKeyword "default"  *> optional clsSym) <*> pParens (sepSEBy pType comma)
  <|> KindSign     <$> (pKeyword "type"     *> pTypeIdentSym) <*> (dcolon *> pKind)
  <|> mkPattern    <$> (pKeyword "pattern"  *> pPatSyn)
  <|> Sign         <$> (pKeyword "pattern"  *> sepEndBy1 pUIdentSym comma <* dcolon) <*> pType
  <|> StandDeriving<$> (pKeyword "deriving" *> pStrat) <*> pure 0 <*> (pKeyword "instance" *> pType)
  <|> noop         <$  (pKeyword "type"     <* pKeyword "role" <* pTypeIdentSym <*
                                               some (pKeyword "nominal" <|> pKeyword "phantom" <|> pKeyword "representational"))
  where
    pFunDeps = (bar *> sepSEBy1 pFunDep comma) <|> pure []

    clsSym = do s <- pUIdentSym <|> pLIdentSymbol; guard (unIdent s /= "()"); return s

    mkPattern (lhs, pat, meqn) = Pattern lhs pat meqn
    noop = Infix (AssocLeft, 0) []        -- harmless definition

    pStrat = (DerVia <$> (pKeyword "via" *> pType)) <|> pSimpleStrat

    pFExpr = EVar <$> (pLQIdentSym <|> pUQIdentSym)

    pSafety = pKeyword "unsafe" <|> pKeyword "safe" <|> pKeyword "interruptible"

pCallConv :: P CallConv
pCallConv = (Cccall <$ pKeyword "ccall") <|> (Ccapi <$ pKeyword "capi") <|> (Cjavascript <$ pKeyword "javascript")

-- Type families, associated types, and data families.
-- These come before the regular data/newtype/type alternatives in pDef.

-- 'type family F a ...' with optional result kind/injectivity and equations.
pTypeFamily :: P EDef
pTypeFamily = do
  pKeyword "type"
  pKeyword "family"
  lhs <- pLHS
  (mk, injVars) <- pResultKindInj
  let inj = lhsInjFlags lhs injVars
  (TypeFam lhs mk inj . Just <$> (pKeyword "where" *> pBlock pTypeFamEqn))
    <|> pure (TypeFam lhs mk inj Nothing)

-- 'type instance F t1 t2 = rhs'
pTypeInstance :: P EDef
pTypeInstance = do
  pKeyword "type"
  pKeyword "instance"
  vks <- pForall
  (fn, args) <- pFamHead
  rhs <- equal *> pType
  pure (TypeInst vks fn args rhs)

-- 'data family D a ...' with optional result kind.
pDataFamily :: P EDef
pDataFamily = do
  pKeyword "data"
  pKeyword "family"
  lhs <- pLHS
  mk <- pResultKindAnn
  pure (DataFam lhs mk)

-- 'data instance D t1 t2 ...' with constructors, GADT constructors, or none.
pDataInstance :: P EDef
pDataInstance = do
  pKeyword "data"
  pKeyword "instance"
  vks <- pForall
  (fn, args) <- pFamHead
  (cs, ds) <- pDataInstRest vks fn args
  pure (DataInst False vks fn args cs ds)

-- 'newtype instance N t1 t2 = Con ...' (always a single constructor).
pNewtypeInstance :: P EDef
pNewtypeInstance = do
  pKeyword "newtype"
  pKeyword "instance"
  vks <- pForall
  (fn, args) <- pFamHead
  c <- equal *> pField
  ds <- pDerivings
  pure (DataInst True vks fn args [c] ds)

-- The body of a 'data instance' after its head:
-- '= constrs', 'where' GADT constructors, or nothing, then derivations.
pDataInstRest :: [IdKind] -> Ident -> [EType] -> P ([Constr], [Deriving])
pDataInstRest vks fn args = do
  cs <- (equal *> sepBy1 (addVks <$> pConstr) bar)
    <|> (concatMap (dsGADTInst vks fn args) <$> (pKeyword "where" *> pBlock pGADTconstr))
    <|> pure []
  ds <- pDerivings
  pure (cs, ds)
  where addVks (Constr evks ctx c inf ets) = Constr (vks ++ evks) ctx c inf ets

-- One closed type family equation: '[forall ... .] F pat ... = rhs'.
pTypeFamEqn :: P TypeEqn
pTypeFamEqn = do
  vks <- pForall
  (_, args) <- pFamHead
  rhs <- equal *> pType
  pure (vks, args, rhs)

-- Optional result kind and injectivity annotation on a family head:
--   ':: kind'                       a result kind
--   '= (r :: kind) | r -> deps'      injectivity with kind
--   '= r | r -> deps'               injectivity without kind
--   nothing                         neither
pResultKindInj :: P (Maybe EKind, [Ident])
pResultKindInj =
        ((\ k -> (Just k, [])) <$> (dcolon *> pKind))
    <|> (do
          equal
          (rVar, mk) <- pParens ((,) <$> pLIdentSym <*> (Just <$> (dcolon *> pKind)))
                    <|> ((\ r -> (r, Nothing)) <$> pLIdentSym)
          fds <- (bar *> sepSEBy1 pFunDep comma) <|> pure []
          let injVars = [ dep | ([lhsVar], rhsVars) <- fds, unIdent lhsVar == unIdent rVar, dep <- rhsVars ]
          pure (mk, injVars))
    <|> pure (Nothing, [])

pResultKindAnn :: P (Maybe EKind)
pResultKindAnn = fst <$> pResultKindInj

-- Injective argument flags: True at 0-based argument positions determined
-- by the result variable alone, or [] when no injectivity is declared.
lhsInjFlags :: LHS -> [Ident] -> [Bool]
lhsInjFlags (_, vks) injVars
  | null injVars = []
  | otherwise    = [ any (\ v -> unIdent v == unIdent (idKindIdent vk)) injVars | vk <- vks ]

-- Parse a family equation/instance head (prefix, parenthesized, or infix)
-- into the family name and its argument types.
pFamHead :: P (Ident, [EType])
pFamHead = do
  t <- pType
  case splitFamHead t of
    Just r  -> pure r
    Nothing -> errorMessage (E.getSLoc t) $ "bad family head " ++ prettyShow t

-- Decompose a head type into the family name and argument types.
splitFamHead :: EType -> Maybe (Ident, [EType])
splitFamHead = go []
  where
    go args (EApp f a) = go (a : args) f
    go args (EParen e) = go args e
    go args (ESign e _) = go args e
    go args (EForall _ _ e) = go args e
    go args (EOper e1 [(op, e2)]) = Just (op, e1 : e2 : args)
    go args (EVar i) = Just (i, args)
    go _ _ = Nothing

-- Transform a GADT-style data instance constructor against the instance head.
-- When the result type matches the head, the argument equalities become
-- constraints; otherwise the constructor is kept as is (still parses).
dsGADTInst :: [IdKind] -> Ident -> [EType] -> ([Ident], [IdKind], [EConstraint], Either [SType] [ConstrField], EType) -> [Constr]
dsGADTInst vks fn args (cnms, es, ctx, ets, rty) = map mk cnms
  where
    mk cnm =
      case splitFamHead rty of
        Just (fn', rargs) | fn' == fn, length rargs == length args ->
          Constr (vks ++ es ++ extraKinds) (zipWith mkEq args rargs ++ ctx) cnm False ets
        _ -> Constr (vks ++ es) ctx cnm False ets
    extraKinds = map (\ i -> IdKind i (EVar dummyIdent)) (freeTyVars (rty : etsTypes ets) \\ map idKindIdent (vks ++ es))
    mkEq t1 t2 = EApp (EApp (EVar (mkIdent "~")) t1) t2

-- The argument types of a constructor, positional or named.
etsTypes :: Either [SType] [ConstrField] -> [EType]
etsTypes = either (map snd) (map (snd . snd))

-- A single functional dependency: 'xs -> ys'.
pFunDep :: P FunDep
pFunDep = (,) <$> some pLIdent <*> (pSRArrow *> some pLIdent)

pPatSyn :: P (LHS, EPat, Maybe [Eqn])
pPatSyn = do
  lhs@(i, vs) <- pRecLHS <|> pLHS
  ( do equal;
       p <- pPat
       guard (isExp p)
       let eqn = eEqn (map (EVar . idKindIdent) vs) p
       pure (lhs, p, Just [eqn])
   ) <|> (
    do pSLArrow
       p <- pPat
       meqns <- optional (pKeyword "where" *> pBraces (pEqnsU i))
       pure (lhs, p, fmap snd meqns)
   )
  where
    -- A record pattern synonym head: 'Con { f1, f2, ... }'.
    -- Tag the field kinds with '$recpat' so TypeCheck generates record
    -- selectors and ConSyn field metadata while keeping AST compatibility.
    pRecLHS = do
      i <- pUIdentSym
      fs <- pSpec '{' *> sepSEBy pLIdentSym comma <* pSpec '}'
      pure (i, [IdKind f (EVar (mkIdent "$recpat")) | f <- fs])

dcolon :: P ()
dcolon = pSymbol "::" <|> pSymbol "\x2237"

-- Is a pattern also an expression?
-- (Used to recognize unidirectional pattern synonyms; be generous so that
-- valid right-hand sides like 'C (x :| [])' are accepted.)
isExp :: Expr -> Bool
isExp (EVar _) = True
isExp (EListish (LList es)) = all isExp es
isExp (EListish _) = True
isExp (ETuple es) = all isExp es
isExp (EApp e1 e2) = isExp e1 && isExp e2
isExp (EOper e1 ies) = isExp e1 && all (isExp . snd) ies
isExp (EUpdate e fs) = isExp e && all isExpField fs
  where isExpField (EField _ fe) = isExp fe
        isExpField _             = True
isExp (ELit _ _) = True
isExp (EQLit _ _ _) = True
isExp (EParen e) = isExp e
isExp (ESign e _) = isExp e
isExp (ENegApp e) = isExp e
isExp (ETypeArg _) = True
isExp (ESelect _) = True
isExp (ELam _ _) = True
isExp (ECase _ _) = True
isExp (EDo _ _) = True
isExp (ESectL e _) = isExp e
isExp (ESectR _ e) = isExp e
isExp (EIf e1 e2 e3) = isExp e1 && isExp e2 && isExp e3
isExp (EMultiIf _) = True
isExp _ = False

pData :: P (LHS, [Constr])
pData = do
  (tnm, vks) <- pLHS
  mk <- optional (dcolon *> pKind)
  let lhs = case mk of
              Nothing -> (tnm, vks)
              Just k  ->
                let (_, k') = unForall k
                    aks = splitKindArrows k'
                    kvks = [ IdKind (mkIdentSLoc (slocIdent tnm) ("$gk" ++ show i)) ak
                           | (i, ak) <- zip [0 :: Int ..] aks ]
                in  (tnm, vks ++ kvks)
      pConstrs = equal *> sepBy1 pConstr bar
  ((,) lhs <$> pConstrs)
   <|> pGADT lhs
   <|> pure (lhs, [])
  where
    splitKindArrows (EOper e0 ops) = init (go e0 [] ops)
      where
        mkSeg a [] = a
        mkSeg a r  = EOper a (reverse r)
        go cur acc [] = [mkSeg cur acc]
        go cur acc ((op, e) : rest)
          | unIdent op == "->" || unIdent op == "\x2192" = mkSeg cur acc : go e [] rest
          | otherwise = go cur ((op, e) : acc) rest
    splitKindArrows t = fst (getArrows t)

pGADT :: LHS -> P (LHS, [Constr])
pGADT (n, vks) = do
  let f (IdKind i k) = IdKind (addIdentSuffix i "$") k
      lhs = (n, map f vks)
  pKeyword "where"
  gs <- pBlock pGADTconstr
  pure (lhs, concatMap (dsGADT lhs) gs)

-- A GADT constructor, possibly with several comma-separated names, and
-- either positional argument types or a record declaration:
--   C1, C2 :: forall ... . ctx => t1 -> t2 -> Res
--   C :: forall ... . ctx => { f1, f2 :: !T1, f3 :: T2 } -> Res
pGADTconstr :: P ([Ident], [IdKind], [EConstraint], Either [SType] [ConstrField], EType)
pGADTconstr = do
  cns <- sepEndBy1 pUIdentSym comma
  dcolon
  es <- pForall
  ctx <- pContext
  let pGType = pStrictP $ pOperators pOper pTypeArg
  flds <- (Right <$> (pRecFields <* pSRArrow))
      <|> (Left <$> many (pGType <* pSRArrow))
  res <- pType
  pure (cns, es, ctx, flds, res)

dsGADT :: LHS -> ([Ident], [IdKind], [EConstraint], Either [SType] [ConstrField], EType) -> [Constr]
dsGADT (tnm, vks) (cnms, es, ctx, ets, rty) = map mk cnms
  where
    mk cnm =
      case getAppM rty of
        Just (tnm', ts) | tnm == tnm' && length vks == length ts ->
            -- Check if we can use a regular constructor
            case zipWithM mtch vks ts of
              -- Result type is just type variables, so use it as is
              Just sub | not (anySame (map fst sub))
                -> Constr es'' ctx'' cnm False ets'
                            where ets' = case ets of
                                           Left  stys -> Left (map (second $ subst sub) stys)
                                           Right fs   -> Right [(f, (s, subst sub t)) | (f, (s, t)) <- fs]
                                  ctx'' = map (subst sub) ctx
                                  es'' = if null es then kind (freeTyVars (etsTypes ets) \\ map fst sub) else es
              _ -> Constr es'  ctx' cnm False ets
          where es' = if null es then kind (freeTyVars (rty : etsTypes ets)) else es
                ctx' = zipWith (\ (IdKind i _) t -> eq (EVar i) t) vks ts ++ ctx
                eq t1 t2 = EApp (EApp (EVar (mkIdentSLoc (E.getSLoc t1) "~")) t1) t2
                mtch (IdKind i _) (EVar i') | not (isConIdent i') = Just (i', EVar i)
                mtch _ _ = Nothing
                kind = map (\ i -> IdKind i (EVar dummyIdent))
        _ -> errorMessage (E.getSLoc rty) $ "Bad GADT result type " ++ prettyShow (rty, tnm, vks)

pDerivings :: P [Deriving]
pDerivings = many pDeriving

pDeriving :: P Deriving
pDeriving = pKeyword "deriving" *> (    (flip Deriving <$> pDer <*> pVia)
                                    <|> (Deriving <$> pSimpleStrat <*> pDer) )
  where pDer = map ((,) 0) <$>
                   (    pParens (sepSEBy pType comma)
                    <|> ((:[]) <$> pAType) )
        pVia = DerVia <$> (pKeyword "via" *> pType)

pSimpleStrat :: P DerStrategy
pSimpleStrat = (DerStock <$ pKeyword "stock") <|> (DerNewtype <$ pKeyword "newtype")
           <|> (DerAnyClass <$ pKeyword "anyclass") <|> pure DerNone

-- List has 0 or 1 elements
pContext :: P [EConstraint]
pContext = (pCtx <* pDRArrow) <|> pure []
  where
    pCtx = (:[]) <$> pOperators pOper pTypeArg

pDRArrow :: P ()
pDRArrow = pSymbol "=>" <|> pSymbol "\x21d2"

pSRArrow :: P ()
pSRArrow = pSymbol "->" <|> pSymbol "\x2192"

pSLArrow :: P ()
pSLArrow = pSymbol "<-" <|> pSymbol "\x2190"

pConstr :: P Constr
pConstr = ((\ vs ct t1 c t2 -> Constr vs ct c True (Left [t1, t2])) <$> pForall <*> pContext <*> pSTypeApp <*> pConstrOper <*> pSTypeApp)
      <|> (Constr <$> pForall <*> pContext <*> pUIdentSym <*> pure False <*> pFields)


pFields :: P (Either [SType] [(Ident, SType)])
pFields = Right <$> pRecFields
      <|> Left  <$> many pSAType

-- Record fields: '{ f1, f2 :: !T1, f3 :: T2 }'.
pRecFields :: P [(Ident, SType)]
pRecFields = pSpec '{' *> (concatMap flat <$> sepSEBy ((,) <$> (sepEndBy1 pLIdentSym comma <* dcolon) <*> pSType) comma <* pSpec '}')
  where flat (is, t) = [ (i, t) | i <- is ]

-- XXX This is a mess.
pSAType :: P (Bool, EType)
pSAType = pStrictP pAType
pSType :: P (Bool, EType)
pSType  = pStrictP pType
pSTypeApp :: P (Bool, EType)
pSTypeApp  = do
  s <- pStrict
  t <- if s then pAType else pTypeApp
  pure (s, t)
pStrict :: P Bool
pStrict = (True <$ pSpec '!') <|> pure False
pStrictP :: P a -> P (Bool, a)
pStrictP p = (,) <$> pStrict <*> p

pLHS :: P LHS
pLHS =  (,)                         <$> pTypeIdentSym <*> many pIdKind
    <|> (\ a c b    -> (c, [a,b]))  <$> pIdKind <*> pSymOper <*> pIdKind
    <|> (\ a c b as -> (c, a:b:as)) <$> (lpar *> pIdKind) <*> pSymOper <*> (pIdKind <* rpar) <*> many pIdKind
    <|> (\ a c      -> (c, [a]))    <$> (lpar *> pIdKind) <*> (pSymOper <* rpar)

pImportSpec :: P ImportSpec
pImportSpec =
  let
    pSource = (ImpBoot <$ pPragma "SOURCE") <|> pure ImpNormal
    pQualified = True <$ pKeyword "qualified"
    -- the 'qualified' can occur before or after the module name
    pQId =      ((,) <$> pQualified <*> pUQIdentA)
            <|> ((\ a b -> (b,a)) <$> pUQIdentA <*> (pQualified <|> pure False))
    imp a (b, c) = ImportSpec a b c
  in  imp <$> pSource <*> pQId <*> optional (pKeyword "as" *> pUQIdent) <*>
              optional ((,) <$> ((True <$ pKeyword "hiding") <|> pure False) <*> pParens (sepSEBy pImportItem comma))

pImportItem :: P ImportItem
pImportItem =
      impType     <$> pUQIdentSym <*> pParens pConList
  <|> ImpTypeSome <$> pUQIdentSym <*> pure []
  <|> ImpValue    <$> pLQIdentSym
  <|> ImpValue    <$> (pKeyword "pattern" *> pUQIdentSym)
  <|> impType     <$> (pKeyword "type" *> (pUQIdentSym <|> pLQIdentSymbol)) <*> (pParens pConList <|> pure [])
  where impType i [d] | d == dotDotIdent = ImpTypeAll  i
        impType i is                     = ImpTypeSome i is

pConList :: P [Ident]
pConList = sepSEBy (pDotDot <|> pQIdent <|> pUIdentSpecial <|> pParens pSymOper) comma
  where pDotDot = dotDotIdent <$ pSymbol ".."

dotDotIdent :: Ident
dotDotIdent = mkIdent ".."

--------
-- Types

pIdKind :: P IdKind
pIdKind =
      ((\ i -> IdKind i (EVar dummyIdent)) <$> pLIdentSym)          -- dummyIdent indicates that we have no kind info
  <|> pParens (IdKind <$> pLIdentSym <*> (dcolon *> pKind))

pKind :: P EKind
pKind = pType

--
-- Partial copy of pExpr, but that includes '->'.
-- Including '->' in pExprOp interacts poorly with '->'
-- in lambda and 'case'.
pType :: P EType
pType = pTypeOp

pForall' :: P [IdKind]
pForall' = forallKW *> some pIdKind
  where forallKW = pKeyword "forall" <|> pSymbol "\x2200"

pForall :: P [IdKind]
pForall = (pForall' <* pSymbol ".") <|> pure []

pTypeOp :: P EType
pTypeOp = pOperators pTypeOper pTypeArg

pTypeOper :: P Ident
pTypeOper = pOper <|> (mkIdent "->" <$ pSRArrow) <|> (mkIdent "=>" <$ pDRArrow)

pTypeArg :: P EType
pTypeArg =
    do
      vs <- pForall'
      q <- (QExpl <$ pSymbol ".") <|> (QReqd <$ pSRArrow)
      EForall q vs <$> pType
  <|>
    pTypeApp

pTypeApp :: P EType
pTypeApp = do
  f <- pAType
  as <- many pAType
  pure $ foldl EApp f as

pAType :: P Expr
pAType =
      (EVar <$> pLQIdentSym)
  <|> (EVar <$> pUQIdentSym)
  <|> pLit
  <|> (eTuple <$> (lpar *> sepBy pType comma <* rpar))
  <|> (EListish . LList . (:[]) <$> (lbra *> pType <* rbra))  -- Unlike expressions, only allow a single element.
  <|> (uTupleTAp <$> (pSpec 'L' *> sepBy  pType comma <* pSpec 'R'))
  <|> (uSumTAp <$> (pSpec 'L' *> sepBy1 pType bar <* pSpec 'R'))
  <|> (uSumT <$> getSLoc <*> (succ . length <$> (pSpec 'L' *> many bar <* pSpec 'R')))
  <|> pPromoted
  <|> (flip EApp <$> (lpar *> pTypeApp) <*> (EVar <$> (pTypeOper <* rpar)))

-- A DataKinds promoted list/tuple type: '[], '[t1, t2], '(), '(t1, t2), '(,,).
-- In MicroHs (Type :: Type) promoted tuples are just tuples, while promoted
-- constructors ('Con, ':, ...) parse as ordinary identifiers elsewhere.
pPromoted :: P EType
pPromoted = do
  loc <- getSLoc
  pSpec '\''
  (do lbra
      ts <- sepBy pType comma
      rbra
      pure (foldr (\ x acc -> eApp2 (EVar (mkIdentSLoc loc "':")) x acc)
                  (EVar (mkIdentSLoc loc "'[]")) ts))
   <|> (do lpar
           (do rpar
               pure (EVar (mkIdentSLoc loc "'()")))
            <|> (do cs <- some comma
                    rpar
                    pure (EVar (mkIdentSLoc loc (map (const ',') cs))))
            <|> (do ts <- sepBy pType comma
                    rpar
                    pure (eTuple ts)))

-------------
-- Patterns

-- Sadly pattern and expression parsing cannot be joined because the
-- use of '->' in 'case' and lambda makes it weird.
-- Instead this is just a copy of some of the expression rules.
-- XXX This can probably be joined with pExpr again now that pType
-- is separate.
pAPat :: P EPat
pAPat =
      (do
         i <- pLIdentSym
         (pSpec '@' *> (EAt i <$> pAPat)) <|> pure (EVar i)
      )
  <|> (evar <$> pUQIdentSym <*> optional pPatUpdate)
  <|> pLit
  <|> (lpar *> (eTuple <$> sepBy pPatV comma <* rpar))
  <|> (lbra *> (EListish . LList <$> sepBy1 pPat comma <* rbra))
  <|> (EViewPat <$> (lpar *> pExpr) <*> (pSRArrow *> pPat <* rpar))
  <|> (pSpec '~' *> (ELazy True  <$> pAPat))
  <|> (pSpec '!' *> (ELazy False <$> pAPat))
  <|> (lpar *> (EOr <$> sepBy1 pPat semi <* rpar))  -- if there is a single pattern it will be matched by the tuple case
  <|> (uTuple <$> (pSpec 'L' *> sepBy pPat comma <* pSpec 'R'))
  <|> pUSummand pPat
  where evar v Nothing = EVar v
        evar v (Just upd) = EUpdate (EVar v) upd

pPatV :: P EPat
pPatV = (EViewPat <$> pExpr <*> (pSRArrow *> pPat)) <|> pPat

pUSummand :: P Expr -> P Expr
pUSummand p = do
  pSpec 'L'
  l <- length <$> many bar
  e <- p
  r <- length <$> many bar
  pSpec 'R'
  let n = l + r
  guard (n > 0)
  pure $ uSummand (n+1) l e

pPat :: P EPat
pPat = pPatOp
  -- This is where view patterns belong, but it's too slow
--   <|> (EViewPat <$> pExpr <*> (pSRArrow *> pPat))

pPatOp :: P EPat
pPatOp = pOperators pUOper pPatArg

pPatArg :: P EPat
pPatArg = (pSymbol "-" *> (ENegApp <$> pNumLit)) <|> pPatApp

pPatApp :: P EPat
pPatApp = do
  f <- pAPat
  as <- many pAPat
  guard (null as || isPConApp f)
  pure $ foldl EApp f as

-- We prefer x = ... to be parsed as a Fcn
-- rather than a PatBind
pPatNotVar :: P EPat
pPatNotVar = guardM pPat notVar
  where notVar (EVar i) = isConIdent i
        notVar _ = True

-------------

-- Regular function definition
pEqns :: P (Ident, [Eqn])
pEqns = pEqns' pLIdentSym pLOper (\ _ _ -> True)
  where pLOper = guardM pOper (not . isConIdent)

-- Pattern synonym function; must have name i.
pEqnsU :: Ident -> P (Ident, [Eqn])
pEqnsU i = pEqns' pUIdentSym pUOper (\ n _ -> i == n)

-- pEqns' is used to parse ordinary function definitions as well
-- as the 'constructor' of pattern synonyms, which has an upper case identifier.
pEqns' :: P Ident -> P Ident -> (Ident -> Int -> Bool) -> P (Ident, [Eqn])
pEqns' ident oper test = do
  (name, eqn@(Eqn ps alts)) <- pEqn ident oper test
  case (ps, alts) of
    ([], EAlts [_] []) ->
      -- don't collect equations when of the form 'i = e'
      pure (name, [eqn])
    _ -> do
      neqns <- many (semi *> pEqn ident oper (\ n l -> n == name && l == length ps))
      pure (name, eqn : map snd neqns)

pEqn :: P Ident -> P Ident -> (Ident -> Int -> Bool) -> P (Ident, Eqn)
pEqn ident oper test = do
  (name, pats) <- pEqnLHS ident oper
  alts <- pAlts equal
  guard (test name (length pats))
  pure (name, Eqn pats alts)

pEqnLHS :: P Ident -> P Ident -> P (Ident, [EPat])
pEqnLHS ident oper =
  ((\ p1 i p2 -> (i, [p1,p2])) <$> pPatApp <*> oper <*> pPatApp)
  <|>
  ((,) <$> ident <*> many pAPat)
  <|>
  ((\ (i, ps1) ps2 -> (i, ps1 ++ ps2)) <$> pParens (pEqnLHS ident oper) <*> many pAPat)

pAlts :: P () -> P EAlts
pAlts sep = do
  alts <- pAltsL sep
  bs <- pWhere pBind
  pure (EAlts alts bs)

pAltsL :: P () -> P [EAlt]
pAltsL sep =
      some (pAlt sep)
  <|> ((\ e -> [([], e)]) <$> (sep *> pExpr))

pAlt :: P () -> P EAlt
pAlt sep = (,) <$> (bar *> sepSEBy1 pStmt comma) <*> (sep *> pExpr)

pWhere :: P EBind -> P [EBind]
pWhere pb =
      (pKeyword "where" *> pBlock pb)
  <|> pure []

-------------
-- Statements

pStmt :: P EStmt
pStmt =
      (SRec  <$> (pKeyword "rec" *> (pBlock pStmt <|> ((:[]) <$> pRecSingle))))
  <|> pRecSingle
  <|> (SThen <$> pExpr)
  where pRecSingle =
              (SBind <$> (pPat <* pSLArrow) <*> pExpr)
          <|> (sLet  <$> (pKeyword "let" *> pBlock pBind)) <*> optional (pKeyword "in" *> pExpr)
        sLet b Nothing  = SLet b
        sLet b (Just i) = SThen (ELet b i)

-------------
-- Expressions

pExpr :: P Expr
pExpr = pExprOp

pExprArg :: P Expr
pExprArg = pExprApp <|> pLam <|> pCase <|> pLet <|> pIf <|> pDo

pExprApp :: P Expr
pExprApp = do
  f <- pAExpr
  as <- many pAExprArg
  pure $ foldl EApp f as

pAExprArg :: P Expr
pAExprArg = pAExpr <|> pLam <|> pCase <|> pLet <|> pIf <|> pDo

pLam :: P Expr
pLam = do
  loc <- getSLoc
  pSpec '\\' *>
    (    eLamWithSLoc loc <$> some pAPat <*> (pSRArrow *> pExpr)
     <|> eLamCase loc <$> (pKeyword "case" *> pBlock pCaseArm)
    )

eLamCase :: SLoc -> [ECaseArm] -> Expr
eLamCase loc as = ELam loc [ Eqn [p] a | (p, a) <- as ]

pCase :: P Expr
pCase = ECase <$> (pKeyword "case" *> pExpr) <*> (pKeyword "of" *> pBlock pCaseArm)

pCaseArm :: P ECaseArm
pCaseArm = (,) <$> pPat <*> pAlts pSRArrow

pLet :: P Expr
pLet = ELet <$> (pKeyword "let" *> pBlock pBind) <*> (pKeyword "in" *> pExpr)

pDo :: P Expr
pDo = do
  (q, rec) <- ((\ i -> (Just i, False)) <$> pQualDo) <|> ((Nothing, False) <$ pKeyword "do") <|> ((Nothing, True) <$ pKeyword "mdo")
  ss <- pBlock pStmt
  guard (not (null ss))
  if rec then
    case last ss of
      SThen e ->
        pure $ EDo q [SRec (init ss), SThen e]
      _ -> Control.Monad.Fail.fail "mdo"
   else
    pure (EDo q ss)

pIf :: P Expr
pIf = EIf <$> (pKeyword "if" *> pExpr) <*>
              (optional semi *> pKeyword "then" *> pExpr) <*>
              (optional semi *> pKeyword "else" *> pExpr)
  <|> EMultiIf <$> (EAlts <$> (pKeyword "if" *> (concat <$> pBlock (some (pAlt pSRArrow)))) <*> pure [])

pQualDo :: P Ident
pQualDo = do
  let
    is (TIdent loc qs@(_:_) "do") = Just (mkIdentSLoc loc (intercalate "." qs))
    is _ = Nothing
  satisfyM "QualDo" is

pOperComma :: P Ident
pOperComma = pOper <|> pComma
  where
    pComma = mkIdentSLoc <$> getSLoc <*> ("," <$ comma)

-- No right section for '-'.
pOperCommaNoMinus :: P Ident
pOperCommaNoMinus = guardM pOperComma (/= mkIdent "-")

-- Updates and selections can be mixed, as in GHC: e.a{x = 1}.b
-- A run of selections becomes one ESelect.
pAExpr :: P Expr
pAExpr = do
  ee <- pAExpr'
  ps <- many (Left <$> pUpdate <|> Right <$> pSelect)
  let post e [] = e
      post e (Left us : r) = post (EUpdate e us) r
      post e r = let (ss, r') = span isRight r
                 in  post (EApp (ESelect (rights ss)) e) r'
  pure $ post ee ps

pUpdate :: P [EField]
pUpdate = pUpdateWith pExpr

pPatUpdate :: P [EField]
pPatUpdate = pUpdateWith pPatV

pUpdateWith :: P Expr -> P [EField]
pUpdateWith pe = pSpec '{' *> sepSEBy pEField comma <* pSpec '}'
  where
    pEField = do
      fs <- (:) . unQualIdent <$> pLQIdentSym <*> many pSelect
      EField fs <$> (equal *> pe) <|> pure (EFieldPun fs)
     <|>
      (EFieldWild <$ pSymbol "..")

pSelect :: P Ident
pSelect = pSpec '.' *> pLIdent

pAExpr' :: P Expr
pAExpr' =
      (EVar   <$> pLQIdentSym)
  <|> (EVar   <$> pUQIdentSym)
  <|> pLit
  <|> pParenOrTuple
  <|> (lbra *> (EListish <$> pListish) <* rbra)
  <|> (lpar *> (ESectL <$> pExprOp) <*> (pOperComma <* rpar))
  <|> (lpar *> (ESectR <$> pOperCommaNoMinus) <*> (pExprOp <* rpar))
  <|> (lpar *> (ESelect <$> some pSelect <* rpar))
  <|> (pKeyword "_primitive" *> (ELit noSLoc . LPrim <$> pString))
  <|> (pSpec '@' *> (ETypeArg <$> pAType))
  <|> (pSpec 'L' *> (uTuple <$> sepBy pExpr comma <* pSpec 'R'))
  <|> pUSummand pExpr
  -- This weirdly slows down parsing
  -- <?> "aexpr"

pParenOrTuple :: P Expr
pParenOrTuple = do
  loc <- getSLoc
  lpar
  m1 <- optional pExpr
  case m1 of
    Nothing ->
      (rpar *> pure (eTuple []))
      <|> (mkTupleSection loc . (Nothing :) <$> (some (comma *> optional pExpr) <* rpar))
    Just e1 ->
      (rpar *> pure (eTuple [e1]))
      <|> (mkTupleOrSection loc . (Just e1 :) <$> (some (comma *> optional pExpr) <* rpar))

mkTupleOrSection :: SLoc -> [Maybe Expr] -> Expr
mkTupleOrSection loc ms
  | all isJust ms = eTuple [ e | Just e <- ms ]
  | otherwise     = mkTupleSection loc ms

mkTupleSection :: SLoc -> [Maybe Expr] -> Expr
mkTupleSection loc ms =
  let (vs, es) = fill (0 :: Int) ms
      fill _ [] = ([], [])
      fill k (Just e  : rest) = let (vs', es') = fill k rest in (vs', e : es')
      fill k (Nothing : rest) =
        let v = mkIdentSLoc loc ("$ts" ++ show k)
            (vs', es') = fill (k + 1) rest
        in  (EVar v : vs', EVar v : es')
  in  eLamWithSLoc loc vs (eTuple es)

pListish :: P Listish
pListish = do
  e1 <- pExpr
  let
    pMore = do
      e2 <- pExpr
      ((\ es -> LList (e1:e2:es)) <$> (some (comma *> pExpr) <* optional comma) )
       <|> (LFromThenTo e1 e2 <$> (pSymbol ".." *> pExpr))
       <|> (LFromThen e1 e2 <$ pSymbol "..")
       <|> pure (LList [e1,e2])
  (comma *> pMore)
   <|> (mkParCompr e1 <$> some (bar *> sepSEBy1 pStmt comma))
   <|> (LFromTo e1 <$> (pSymbol ".." *> pExpr))
   <|> (LFrom e1 <$ pSymbol "..")
   <|> pure (LList [e1])
 <|>  -- List with initial comma
   (comma *> (LList <$> sepEndBy1 pExpr comma))

-- Build a (possibly parallel) list comprehension.
-- A single branch '[e | qs]' is the ordinary comprehension.
-- Multiple branches '[e | qsA | qsB | ...]' zip the branch lists together.
-- The desugaring only uses core syntax (ELet, EVar, ETuple, EListish) plus
-- the always-available list constructors ':' and '[]', so it also works
-- when the Prelude is not imported.
mkParCompr :: Expr -> [[EStmt]] -> Listish
mkParCompr e [qs] = LCompr e qs
mkParCompr e qss = LCompr e [SBind pat (ELet [Fcn zipId zipEqns] zipped)]
  where
    vss = map (nub . concatMap getStmtBound) qss
    lists = zipWith mkList vss qss
    mkList vs qs = EListish (LCompr (tupOf vs) qs)
    zipped = foldl1 (\ a b -> eApp2 (EVar zipId) a b) lists
    pat = foldl1 (\ a b -> ETuple [a, b]) (map tupOf vss)
    -- A branch's bound variables as one tuple pattern/expression:
    -- no variables becomes (), one variable stays bare.
    tupOf []  = ETuple []
    tupOf [v] = EVar v
    tupOf vs  = ETuple (map EVar vs)
    -- A tiny local zip; '$' cannot appear in user code, so no clashes.
    zipId = mkIdent "$parZip"
    x  = mkIdent "$px";  xs = mkIdent "$pxs"
    y  = mkIdent "$py";  ys = mkIdent "$pys"
    cons = mkIdent ":"
    pCons a as = EApp (EApp (EVar cons) (EVar a)) (EVar as)
    zipEqns =
      [ Eqn [pCons x xs, pCons y ys]
            (oneAlt (EApp (EApp (EVar cons)
                               (ETuple [EVar x, EVar y]))
                          (eApp2 (EVar zipId) (EVar xs) (EVar ys))))
      , Eqn [EVar dummyIdent, EVar dummyIdent]
            (oneAlt (EListish (LList [])))
      ]

pExprOp :: P Expr
pExprOp = pOperators pOper pExprArgNeg

pExprArgNeg :: P Expr
pExprArgNeg = (pSymbol "-" *> (ENegApp <$> pExprArg)) <|> pExprArg

pOperators :: P Ident -> P Expr -> P Expr
pOperators oper one = do
  r <- pOperators' oper one
  mt <- optional (dcolon *> pType)
  pure $ maybe r (ESign r) mt

pOperators' :: P Ident -> P Expr -> P Expr
pOperators' oper one = eOper <$> one <*> many ((,) <$> oper <*> one)
  where eOper e [] | notNeg e = e
        eOper e ies = EOper e ies
        notNeg (ENegApp _) = False
        notNeg _ = True

-------------
-- Bindings

-- Bindings allowed in a let
pBind :: P EBind
pBind =
      pBind'
  <|> PatBind     <$> pPatNotVar <*> (EMultiIf <$> pAlts equal)

-- Bindings allowed in top level, let, class
pBind' :: P EBind
pBind' =
      uncurry Fcn <$> pEqns
  <|> Sign        <$> (sepEndBy1 pLIdentSym comma <* dcolon) <*> (pType <* notEqual)
  <|> Infix       <$> ((,) <$> pAssoc <*> pPrec) <*> sepEndBy1 pTypeOper comma
  where
    pAssoc = (AssocLeft <$ pKeyword "infixl") <|> (AssocRight <$ pKeyword "infixr") <|> (AssocNone <$ pKeyword "infix")
    dig (TInt _ ii) | 0 <= i && i <= 9 = Just i  where i = fromInteger ii
    dig _ = Nothing
    pPrec = satisfyM "digit" dig <|> pure 9
    notEqual :: P ()
    notEqual = do
      t <- nextToken
      case t of
        TSpec _ '=' -> Control.Monad.Fail.fail "notEqual"
        _           -> return ()

-- Bindings allowed in a class definition
pClsBind :: P EBind
pClsBind =
      pBind'
  <|> DfltSign    <$> (pKeyword "default" *> pLIdentSym <* dcolon) <*> pType
  <|> DataFam     <$> (pKeyword "data" *> optional (pKeyword "family") *> pLHS) <*> pResultKindAnn
  <|> mkTI        <$> (pKeyword "type" *> optional (pKeyword "instance") *> pForall) <*> pFamHead <*> (equal *> pType)
  <|> mkTD        <$> (pKeyword "type" *> optional (pKeyword "family") *> pLHS) <*> pResultKindInj <*> pure Nothing
  where
    mkTI vks (fn, args) rhs = TypeInst vks fn args rhs
    mkTD lhs (mk, injVars) _ = TypeFam lhs mk (lhsInjFlags lhs injVars) Nothing

-- Bindings allowed in an instance definition
pInstBind :: P EBind
pInstBind =
      uncurry Fcn <$> pEqns' (unQualIdent <$> pLQIdentSym) pInstOper (\_ _ -> True)
  <|> Sign        <$> (sepEndBy1 pLIdentSym comma <* dcolon) <*> pType
  <|> pInstType
  <|> pInstData
  <|> pInstNewtype
  where
    -- Method names may be qualified ('M.method'); the qualifier is dropped.
    pInstOper = guardM pOper (not . isConIdent)
    -- An associated type instance: 'type [instance] F t1 t2 = rhs'.
    pInstType = do
      pKeyword "type"
      optional (pKeyword "instance")
      vks <- pForall
      (fn, args) <- pFamHead
      rhs <- equal *> pType
      pure (TypeInst vks fn args rhs)
    -- An associated data instance.
    pInstData = do
      pKeyword "data"
      optional (pKeyword "instance")
      vks <- pForall
      (fn, args) <- pFamHead
      (cs, ds) <- pDataInstRest vks fn args
      pure (DataInst False vks fn args cs ds)
    -- An associated newtype instance.
    pInstNewtype = do
      pKeyword "newtype"
      optional (pKeyword "instance")
      vks <- pForall
      (fn, args) <- pFamHead
      c <- equal *> pField
      ds <- pDerivings
      pure (DataInst True vks fn args [c] ds)

-- A single-constructor newtype field (exactly one positional or record field).
pField :: P Constr
pField = Constr [] [] <$> pUIdentSym <*> pure False <*> guardM pFields ((== 1) . either length length)

-------------

-- Unboxed sum type with n alternatives
uSumT :: SLoc -> Int -> EType
uSumT l n = EVar (mkIdentSLoc l $ "B@.USum" ++ show n)

-- Unboxed sum type with arguments
uSumTAp :: [EType] -> EType
uSumTAp ts = eApps (uSumT (E.getSLoc ts) (length ts)) ts

-- Summand i of an n-ary "unboxed" alternative
uSummand :: Int -> Int -> Expr -> Expr
uSummand n i e = EApp (EVar (mkIdentSLoc (E.getSLoc e) ("B@.USum" ++ show n ++ "_" ++ show i))) e

-- Unboxed tuple type with n alternatives
uTupleT :: SLoc -> Int -> Expr
uTupleT l n = EVar (mkIdentSLoc l $ "B@.UProd" ++ show n)

-- Unboxed tuple type
uTupleTAp :: [EType] -> EType
uTupleTAp ts = eApps (uTupleT (E.getSLoc ts) (length ts)) ts

-- Unboxed tuple
uTuple :: [Expr] -> Expr
uTuple = uTupleTAp   -- same name as the type

----------

eTuple :: [Expr] -> Expr
eTuple [e] = EParen e
eTuple es = ETuple es

isAlpha_ :: Char -> Bool
isAlpha_ c = isLower_ c || isUpper c

qualName :: SLoc -> [String] -> String -> Ident
qualName loc qs s = mkIdentSLoc loc (intercalate "." (qs ++ [s]))

-------------

formatFailed :: LastFail Token -> MhsError
formatFailed (LastFail _ ts msgs) =
  MhsSyntaxError (tokensLoc ts) (head (map showToken ts ++ ["EOF"])) (unwords (nub msgs))
