module MicroHs.Abstract(
  compileOpt,
  -- reduce,
  ) where
import qualified Prelude(); import MHSPrelude
import Data.Maybe(isNothing)
import MicroHs.Ident
import MicroHs.Exp
import MicroHs.Expr(Lit(..))
import qualified MicroHs.IdentMap as M

--
-- Used combinators
--   * indicates that the implementation uses an indirection
--   A indicates allocation in the implementation
-- S  x y z   = x z (y z)             A
-- K  x y     = x                     *
-- I  x       = x                     *
-- B  x y z   = x (y z)               A
-- C  x y z   = x z y                 A
-- S' x y z w = x (y w) (z w)         A
-- B' x y z w = x y (z w)             A
-- C' x y z w = x (y w) z             A
-- A  x y     = y                     *
-- U  x y     = y x
-- n@(Y x)    = x n
-- Z  x y z   = x y
-- P  x y z   = z x y                 A
-- R  x y z   = y z x                 A
-- O  x y z w = w x y                 A
-- K2 x y z   = x                     *
-- K3 x y z w = x                     *
-- K4 x y z w v = x                   *
-- C'B x y z w = x z (y w)            A
--

data MaybeApp = NotApp | IsApp Exp Exp

getApp :: Exp -> MaybeApp
getApp ae =
  case ae of
    App f a -> IsApp f a
    _       -> NotApp

isPrim :: String -> Exp -> Bool
isPrim s ae =
  case ae of
    Lit (LPrim ss) -> s == ss
    _       -> False

isK :: Exp -> Bool
isK = isPrim "K"

isI :: Exp -> Bool
isI = isPrim "I"

isB :: Exp -> Bool
isB = isPrim "B"

isC :: Exp -> Bool
isC = isPrim "C"

isC' :: Exp -> Bool
isC' = isPrim "C'"

isY :: Exp -> Bool
isY = isPrim "Y"

isP :: Exp -> Bool
isP = isPrim "P"

isZ :: Exp -> Bool
isZ = isPrim "Z"

{-
isU :: Exp -> Bool
isU = isPrim "U"
-}

isK2 :: Exp -> Bool
isK2 = isPrim "K2"

isK3 :: Exp -> Bool
isK3 = isPrim "K3"

cI :: Exp
cI = Lit (LPrim "I")

cK :: Exp
cK = Lit (LPrim "K")

cS :: Exp
cS = Lit (LPrim "S")

cP :: Exp
cP = Lit (LPrim "P")

cC :: Exp
cC = Lit (LPrim "C")

--------------------

compileOpt :: Exp -> Exp
compileOpt = improveT . toExp . compileExpA

-- Annotated expression with free variables at every node,
-- so abstraction can prune dead subtrees in O(1) per node.
data AExp
  = AAtom Exp
  | AApp (M.Map ()) AExp AExp

fvsA :: AExp -> M.Map ()
fvsA ae =
  case ae of
    AAtom (Var y) -> M.singleton y ()
    AAtom _ -> M.empty
    AApp m _ _ -> m

aAppA :: AExp -> AExp -> AExp
aAppA f a = AApp (M.merge (fvsA f) (fvsA a)) f a

aApp2A :: Exp -> AExp -> AExp -> AExp
aApp2A c x y = aAppA (aAppA (AAtom c) x) y

aApp3A :: Exp -> AExp -> AExp -> AExp -> AExp
aApp3A c x y z = aAppA (aApp2A c x y) z

toExp :: AExp -> Exp
toExp ae =
  case ae of
    AAtom e -> e
    AApp _ f a -> App (toExp f) (toExp a)

compileExpA :: Exp -> AExp
compileExpA ae =
  case ae of
    App f a -> aAppA (compileExpA f) (compileExpA a)
    Lam x a -> abstractA x (compileExpA a)
    _       -> AAtom ae

abstractA :: Ident -> AExp -> AExp
abstractA x ae =
  case ae of
    AAtom (Var y) -> if x == y then AAtom cI else aKA ae
    AAtom _       -> aKA ae
    AApp m f a
      | isNothing (M.lookup x m) -> aKA ae
      | otherwise                -> aSA (abstractA x f) (abstractA x a)

aKA :: AExp -> AExp
aKA e = aAppA (AAtom cK) e

data MaybeAppA = NotAppA | IsAppA AExp AExp

getAppA :: AExp -> MaybeAppA
getAppA ae =
  case ae of
    AApp _ f a -> IsAppA f a
    _          -> NotAppA

isPrimA :: String -> AExp -> Bool
isPrimA s ae =
  case ae of
    AAtom e -> isPrim s e
    _       -> False

aSA :: AExp -> AExp -> AExp
aSA a1 a2 =
 if isPrimA "K" a1 then AAtom cI else
  let
    r = aS2A a1 a2
  in
    case getAppA a1 of
      NotAppA -> r
      IsAppA k1 e1 ->
        if isPrimA "K" k1 then
          case getAppA a2 of
            IsAppA k2 e2 ->
              if isPrimA "K" k2 then
                aKA (aAppA e1 e2)
              else
                aBA e1 a2
            NotAppA ->
              if isPrimA "I" a2 then
                e1
              else
                aBA e1 a2
        else
          r
aS2A :: AExp -> AExp -> AExp
aS2A a1 a2 =
  case getAppA a2 of
    NotAppA -> aS3A a1 a2
    IsAppA k2 e2 ->
      if isPrimA "K" k2 then
        aCA a1 e2
      else
        aS3A a1 a2

aS3A :: AExp -> AExp -> AExp
aS3A a1 a2 =
  let
    r = aApp2A cS a1 a2
  in
    case getAppA a1 of
      NotAppA -> r
      IsAppA be1 e2 ->
        case getAppA be1 of
          NotAppA -> r
          IsAppA b1 e1 ->
            if isPrimA "B" b1 then
              aS'A e1 e2 a2
            else
              r

{-
--aS e1 e2 | trace ("S (" ++ toString e1 ++ ") (" ++ toString e2 ++ ")") False = undefined
aS CK              _           = CI                -- S K e           = I
aS (App CK e1)     (App CK e2) = aK (App e1 e2)    -- S (K e1) (K e2) = K (e1 e2)
aS (App CK e1)     CI          = e1                -- S (K e1) I      = e1
aS (App CK e1)     e2          = cB e1 e2          -- S (K e1) e2     = B e1 e2
aS e1              (App CK e2) = aC e1 e2          -- S e1     (K e2) = C e1 e2
aS (App (App CB e1) e2) e3     = aS' e1 e2 e3      -- S (B e1 e2) e3  = S' e1 e2 e3
aS e1 e2                       = App2 CS e1 e2
-}

aCA :: AExp -> AExp -> AExp
aCA a1 e3 =
  let
    r = aC2A a1 e3
  in
    case getAppA a1 of
      NotAppA -> r
      IsAppA x1 e2 ->
        case getAppA x1 of
          NotAppA -> r
          IsAppA bc e1 ->
            if isPrimA "B" bc then
              aC'A e1 e2 e3
            else if isPrimA "C" bc && isPrimA "I" e1 then
              aApp2A cP e2 e3
--            else if isC bc && isC e1 then
--              app2 cR e2 e3
            else
              r

aC2A :: AExp -> AExp -> AExp
aC2A a1 a2 = aApp2A cC a1 a2

{-
aC (App (App CB e1) e2) e3          = aC' e1 e2 e3      -- C (B e1 e2) e3  = C' e1 e2 e3
aC (Var op)             e2 | Just op' <- lookup op flipOps = App (Var op') e2 -- C op e = flip-op e
aC (App (App C' CI) e2) e3          = app2 CP e2 e3
aC (App (App C' C') e2) e3          = app2 CR e2 e3
aC e1                   e2          = app2 C' e1 e2
-}

aBA :: AExp -> AExp -> AExp
aBA a1 a2 =
  let
    r = aB2A a1 a2
  in
    case getAppA a1 of
      NotAppA -> r
      IsAppA cb ck ->
        if isPrimA "B" cb && isPrimA "K" ck && isPrimA "P" a2 then
          AAtom (Lit (LPrim "O"))
        else
          r

aB2A :: AExp -> AExp -> AExp
aB2A a1 a2 =
  let
    r = aB3A a1 a2
  in
    case getAppA a2 of
      IsAppA x1 x2 ->
        case getAppA x1 of
          IsAppA cb ck ->
            if isPrimA "Y" a1 && isPrimA "B" cb && isPrimA "K" ck then
              x2
            else
              r
          NotAppA ->
            if isPrimA "C" a1 && isPrimA "C" x1 && isPrimA "I" x2 then
              AAtom cP
            else
              r
      NotAppA -> r

aB3A :: AExp -> AExp -> AExp
aB3A a1 a2 =
  if isPrimA "I" a1 then
    a2
  else
    aApp2A (Lit (LPrim "B")) a1 a2

{-
aB (App CB CK) CP             = CO -- Cons
aB CY          (App (App CB CK) e) = e  -- B Y (B K e) = e
aB C'          (App C' CI)    = CP -- Pair
aB CI          e              = e  -- B I e = e
aB e1          e2             = app2 CB e1 e2
-}

aS'A :: AExp -> AExp -> AExp -> AExp
aS'A e1 e2 e3 = aApp3A (Lit (LPrim "S'")) e1 e2 e3

aC'A :: AExp -> AExp -> AExp -> AExp
aC'A e1 e2 e3 = aApp3A (Lit (LPrim "C'")) e1 e2 e3

improveT :: Exp -> Exp
improveT ae =
  case getApp ae of
    NotApp -> ae
    IsApp f a ->
      let
        ff = improveT f
        aa = improveT a
      in
        if isK ff && isI aa then
          Lit (LPrim "A")
{- Using I x --> x does not improve things.
        else if isI ff then
          aa
-}
        else if isB ff && isK aa then
          Lit (LPrim "Z")
        else if isC ff && isI aa then
          Lit (LPrim "U")
        else if isB ff && isB aa then
          Lit (LPrim "B'")
        else if isC ff && isC aa then
          Lit (LPrim "R")
        else if isC' ff && isB aa then
          Lit (LPrim "C'B")
        else if isZ ff && isK aa then
          Lit (LPrim "K2")
{-
-- Using J is a very minor improvement
        else if False && isZ ff && isU aa then
          Lit (LPrim "J")
-}
        else if isZ ff && isK2 aa then
          Lit (LPrim "K3")
        else if isZ ff && isK3 aa then
          Lit (LPrim "K4")
        else
          let
            def =
              case getApp aa of
                IsApp ck e ->
                  if isY ff && isK ck then
                    e
                  else
                    kApp ff aa
                NotApp -> kApp ff aa
          in
            def
{-
            case getApp ff of
              IsApp xf xa ->
                if isK xf then
                  xa
                else
                  def
              NotApp -> def
-}


kApp :: Exp -> Exp -> Exp
kApp (Lit (LPrim "K")) (App (Lit (LPrim ('K':s))) x)
  | s == ""  = App (Lit (LPrim "K2")) x
  | s == "2" = App (Lit (LPrim "K3")) x
  | s == "3" = App (Lit (LPrim "K4")) x
kApp f a = App f a

{-
-- K I      -->  A
-- C I      -->  T
-- B B      -->  B'
-- Y (K e)  -->  e
-- K x y    -->  x
improveT (App f a) =
  case (improveT f, improveT a) of
    (CK,                     CI) -> CA
--    (CI,                      e) -> e
    (CY,               App CK e) -> e
--    (App CK e1,              e2) -> e1
    (e1,                     e2) -> App e1 e2
improveT e = e
-}

--------
-- Possible additions
--
-- Added:
--  R = C C
--  R x y z = (C C x y) z = C y x z = y z x
--
--  Q = C I
--  Q x y z = (C I x y) z = I y x z = y x z
--
-- Added:
--  Z = B K
--  Z x y z = B K x y z = K (x y) z = x y
--
--  ZK = Z K
--  ZK x y z = Z K x y z = (K x) z = x
--
--  C'B = C' B
--  C'B x y z w = C' B x y z w = B (x z) y w = x z (y w)

--  B (B e) x y z = B e (x y) z = e (x y z)
--
--  B' :: (a -> b -> c) -> a -> (d -> b) -> d -> c
--  B' k f g x = k f (g x)
--
-- Common:
--  817: C' B
--  616: B Z
--  531: C' C
--  352: Z K
--  305: C' S
--
--  BZ = B Z
--  BZ x y z w = B Z x y z w = Z (x y) z w = x y z
--
--  C'C = C' C
--  C'C x y z w = C' C x y z w = C (x z) y w = x z w y
--
--  C'B P x y z w = P y (x z) w = w y (x z)

{- This makes very little difference.
   There are only 2 reductions in the entire compiler.
reduce :: Exp -> Exp
reduce e = red e []
  where
    -- No duplication, nor cycles, so no S, S', Y
    red (App f a) as                      = red f (reduce a : as)
    red f (x:as)         | isI          f && xxx "I" = red x as
    red f (x:y:as)       | isPrim "A"   f && xxx "A" = red y as
                         | isPrim "U"   f && xxx "U" = red y (x : as)
                         | isK          f && xxx "K" = red x as
    red f (x:y:z:as)     | isB          f && xxx "B" = red x (App y z : as)
                         | isC          f && xxx "C" = red x (z : y : as)
                         | isPrim "Z"   f && xxx "Z" = red x (y : as)
                         | isP          f && xxx "P" = red z (x : y : as)
                         | isPrim "R"   f && xxx "R" = red y (z : x : as)
                         | isPrim "K2"  f && xxx "K2" = red x as
    red f (x:y:z:w:as)   | isPrim "B'"  f && xxx "B'" = red x (y : App z w : as)
                         | isPrim "C'"  f && xxx "C'" = red x (App y w : z : as)
                         | isPrim "O"   f && xxx "O" = red w (x : y : as)
                         | isPrim "K3"  f && xxx "K3" = red x as
                         | isPrim "C'B" f && xxx "C'B" = red x (z : App y w : as)
    red f (x:_:_:_:_:as) | isPrim "K4"  f && xxx "K4" = red x as

    red f as                              = foldl App f as

    xxx s = trace s True
-}
