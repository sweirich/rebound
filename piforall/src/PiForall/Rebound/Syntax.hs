-- A port of https://github.com/sweirich/pi-forall
-- This version distinguishes between global and local names
-- Global names are strings (which must be unique). Local names
-- are represented by indices.
module PiForall.Rebound.Syntax
  ( module PiForall.Rebound.Syntax,
    GlobalName,
    ConstructorNames (..),
    TyConName (..),
    DataConName (..),
    ModuleImport (..),
    ModuleName (..),
  )
where

import Rebound
import Rebound.Bind.Local qualified as Local
import Rebound.Bind.Pat qualified as Pat
import Rebound.Bind.Scoped (TeleList (..), (<:>))
import Rebound.Bind.Scoped qualified as Scoped
import Rebound.Bind.Single qualified as B
import Rebound.MonadNamed (Named (..))
import Rebound.MonadScoped
import Data.Fin
import Data.Maybe qualified as Maybe
import Data.Set qualified as Set
import Data.Vec qualified as Vec
import PiForall.ConcreteSyntax (ConstructorNames (..), DataConName, GlobalName, ModuleImport (..), ModuleName, TyConName)
import Text.ParserCombinators.Parsec.Pos (SourcePos, newPos)
import Unsafe.Coerce (unsafeCoerce)
import Data.Foldable (fold)

-- | types and terms (combined syntax)
type Typ = Term

data Term (n :: Nat)
  = TyType
  | Lam (Local.Bind Term Term n)
  | Var (Fin n)
  | Global GlobalName
  | Pi (Typ n) (Local.Bind Term Typ n)
  | Pos SourcePos (Term n)
  | Let (Term n) (Local.Bind Term Term n)
  | TyCon TyConName [Typ n]
  | DataCon DataConName [Term n]
  | Case (Term n) [Match n]
  | App (Term n) (Term n)
  | Ann (Term n) (Typ n)
  | -- | Equality type  `a = b`
    TyEq (Term n) (Term n)
  | -- | Proof of equality `Refl`
    TmRefl
  | -- | equality type elimination  `subst a by pf`
    Subst (Term n) (Term n)
  | -- | witness to an equality contradiction
    Contra (Term n)
  | TrustMe
  | PrintMe

-- | Patterns (without embedded type annotations)
-- `p` is the number of variables bound by the pattern
-- LocalName is used for printing only, irrelevant for alpha-equivalence
data Pattern (p :: Nat) where
  PatCon :: DataConName -> Pat.PatList Pattern p -> Pattern p
  PatVar :: LocalName -> Pattern N1

-- A single branch in a match expression. Binds a pattern
-- with expression variables, with an expression body
data Match (n :: Nat)
  = forall p. (SNatI p) => Branch (Pat.Bind Term Term (Pattern p) n)

----------------------------------------------------------
-- Datatype and constructor declarations
----------------------------------------------------------

-- | Local assumption, either declarations of local variables or definitions (i.e. constraints on variables already in scope)
data Local p n where
  LocalDecl :: LocalName -> Typ n -> Local N1 n -- binding assumption
  LocalDef :: Fin n -> Term n -> Local N0 n -- nonbinding assumption

type Telescope = Scoped.TeleList Local

-- | Datatype definitions
data DataDef = forall n.
  DataDef
  { data_delta :: Telescope n Z,
    data_sort :: Typ Z,
    data_constructors :: [ConstructorDef n]
  }

-- | Data constructor definitions, in the scope of the parameters
-- of the datatype
data ConstructorDef n = forall m.
  ConstructorDef
  { con_name :: DataConName,
    con_theta :: Telescope m n
  }

-- A data constructor paired with the telescope of its data type
data ScopedConstructorDef
  = forall n.
    ScopedConstructorDef (Telescope n Z) (ConstructorDef n)

-- Toplevel components of modules
data ModuleEntry
  = ModuleDecl {declName :: GlobalName, declType :: Typ Z}
  | ModuleDef {declName :: GlobalName, declTerm :: Term Z}
  | ModuleData {declName :: GlobalName, declData :: DataDef}
  | ModuleFail {failing :: ModuleEntry}

-- | A Module has a name, a list of imports, a list of declarations,
--   and a set of constructor names (which affect parsing).
data Module = Module
  { moduleName :: ModuleName,
    moduleImports :: [ModuleImport],
    moduleEntries :: [ModuleEntry],
    moduleConstructors :: ConstructorNames
  }

-------------------------------------------------------

-- * Definitions related to datatypes

-- | Is this the syntax of a number?
isNumeral :: Term n -> Maybe Int
isNumeral (Pos _ t) = isNumeral t
isNumeral (DataCon c []) | c == "Zero" = Just 0
isNumeral (DataCon c [t]) | c == "Succ" =
  do n <- isNumeral t; return (n + 1)
isNumeral _ = Nothing

-- | Is this pattern a variable
isPatVar :: Pattern p -> Bool
isPatVar (PatVar _) = True
isPatVar _ = False

strip :: Term n -> Term n
strip (Pos _ tm) = strip tm
strip (Ann tm _) = strip tm
strip tm = tm

-- | Partial inverse of Pos
unPos :: Term n -> Maybe SourcePos
unPos (Pos p _) = Just p
unPos _ = Nothing

-- | Tries to find a Pos inside a term, otherwise just gives up.
unPosFlaky :: Term n -> SourcePos
unPosFlaky t = Maybe.fromMaybe (newPos "unknown location" 0 0) (unPos t)

----------------------------------------------
--  Sized/Named instances
----------------------------------------------

-- simple patterns

instance Sized (Pattern p) where
  type Size (Pattern p) = p
  size (PatCon _ p) = size p
  size (PatVar _) = s1

instance Named LocalName (Pattern p) where
  names :: Pattern p -> Vec p LocalName
  names (PatVar x) = x ::: VNil
  names (PatCon _ p) = names p

-- scoped patterns

instance Sized (Local p n) where
  type Size (Local p n) = p
  size (LocalDecl _ _) = s1
  size (LocalDef _ _) = s0

instance Scoped.ScopedSized (Local p) where
  type ScopedSize (Local p) = p

instance Scoped.IScopedSized Local

instance Named LocalName (Local p n) where
  names (LocalDecl x _) = x ::: VNil
  names (LocalDef _ _) = VNil

----------------------------------------------
--  Subst instances
----------------------------------------------

instance SubstVar Term where
  var = Var

instance Shiftable Term where
  shift = shiftFromApplyE @Term

instance Subst Term Term where
  applyE r TyType = TyType
  applyE r (Lam bnd) = Lam (applyE r bnd)
  applyE r (TyCon c es) = TyCon c (map (applyE r) es)
  applyE r (DataCon c es) = DataCon c (map (applyE r) es)
  applyE r (Pi a b) = Pi (applyE r a) (applyE r b)
  applyE r (Var x) = applyEnv r x
  applyE r (Global n) = Global n
  applyE r (App e1 e2) = App (applyE r e1) (applyE r e2)
  applyE r (Case t brs) = Case (applyE r t) (map (applyE r) brs)
  applyE r (Ann a t) = Ann (applyE r a) (applyE r t)
  applyE r (Let e1 bnd) = Let (applyE r e1) (applyE r bnd)
  applyE r (Pos sp e) = Pos sp (applyE r e)
  applyE r (TyEq a b) = TyEq (applyE r a) (applyE r b)
  applyE r TmRefl = TmRefl
  applyE r (Subst a b) = Subst (applyE r a) (applyE r b)
  applyE r (Contra p) = Contra (applyE r p)
  applyE r TrustMe = TrustMe
  applyE r PrintMe = PrintMe

instance Shiftable Match where
  shift = shiftFromApplyE @Term

instance Subst Term Match where
  applyE r (Branch (b :: Pat.Bind Term Term (Pattern p) n)) =
    Branch (applyE r b)

-- substitution could fail if the constraints in the
-- telescope are not satisifiable. So we define a
-- special purpose substitution operation for that
-- called doSubst in TypeCheck

instance Shiftable (Local p) where
  shift = shiftFromApplyE @Term

instance Subst Term (Local p) where
  applyE r (LocalDecl ln t) =
    LocalDecl ln (applyE r t)
  applyE r (LocalDef x u) =
    case applyE r (Var x) of
      Var y -> LocalDef y (applyE r u)
      _ -> error "Error: cannot substitute left hand side of constraint."

----------------------------------------------
-- Free variable calculation
----------------------------------------------

t00 :: Term N2
t00 = App (Var f0) (Var f0)

t01 :: Term N2
t01 = App (Var f0) (Var f1)

-- >>> appearsFree f0 t00

-- >>> appearsFree f1 t00
-- False

instance FV Term where
  freeVars TyType = Set.empty
  freeVars (Var x) = Set.singleton x
  freeVars (Global _) = Set.empty
  freeVars (Pi a b) = freeVars a `Set.union` freeVars b
  freeVars (Lam b) = freeVars b
  freeVars (App a b) = freeVars a `Set.union` freeVars b
  freeVars (TyCon _ args) = foldMap freeVars args
  freeVars (DataCon _ args) = foldMap freeVars args
  freeVars (Case t b) = freeVars t `Set.union` foldMap freeVars b
  freeVars (Ann a t) = freeVars a `Set.union` freeVars t
  freeVars (Pos _ a) = freeVars a
  freeVars (Let a b) = freeVars a `Set.union` freeVars b
  freeVars (TyEq a b) = freeVars a `Set.union` freeVars b
  freeVars TmRefl = Set.empty
  freeVars (Subst a b) = freeVars a `Set.union` freeVars b
  freeVars (Contra a) = freeVars a
  freeVars TrustMe = Set.empty
  freeVars PrintMe = Set.empty

  appearsFree n t = n `Set.member` freeVars t

instance FV Match where
  freeVars (Branch bnd) = freeVars bnd
  appearsFree n t = n `Set.member` freeVars t

instance FV (Local p) where
  freeVars (LocalDecl x y) = freeVars y
  freeVars (LocalDef x y) = x `Set.insert` freeVars y
  appearsFree n t = n `Set.member` freeVars t

----------------------------------------------
-- weakening (convenience functions)
----------------------------------------------

-- >>> :t weaken' s1 t00
-- weaken' s1 t00 :: Term ('S ('S N1))

-- >>> weaken' s1 t00
-- App (Var 0) (Var 0)

weaken' :: SNat m -> Term n -> Term (m + n)
weaken' m = applyE @Term (weakenE' m)

weakenBind' :: SNat m -> B.Bind Term Term n -> B.Bind Term Term (m + n)
weakenBind' m = applyE @Term (weakenE' m)

-- AXIOM: no need to do anything with terms that are already closed
weakenClosed :: Term Z -> Term m
weakenClosed = unsafeCoerce

-- AXIOM:
weakenTeleClosed :: forall m p. Telescope p Z -> Telescope p m
weakenTeleClosed = unsafeCoerce

----------------------------------------------
-- strengthening
----------------------------------------------

-- >>> strengthen' s1 s1 t00
-- Just (0 0)

-- >>> strengthen' s1 s1 t01
-- Nothing

instance Strengthen Term where
  strengthenRec k m n (Var x) = Var <$> strengthenRec k m n x
  strengthenRec k m n (Global s) = pure (Global s)
  strengthenRec k m n TyType = pure TyType
  strengthenRec k m n (Lam b) = Lam <$> strengthenRec k m n b
  strengthenRec k m n (DataCon c args) = DataCon c <$> mapM (strengthenRec k m n) args
  strengthenRec k m n (TyCon c args) = TyCon c <$> mapM (strengthenRec k m n) args
  strengthenRec k m n (Pi a b) = Pi <$> strengthenRec k m n a <*> strengthenRec k m n b
  strengthenRec k m n (App a b) = App <$> strengthenRec k m n a <*> strengthenRec k m n b
  strengthenRec k m n (Case a b) = Case <$> strengthenRec k m n a <*> mapM (strengthenRec k m n) b
  strengthenRec k m n (Ann a t) = Ann <$> strengthenRec k m n a <*> strengthenRec k m n t
  strengthenRec k m n (Pos p a) = Pos p <$> strengthenRec k m n a
  strengthenRec k m n (Let a b) = Let <$> strengthenRec k m n a <*> strengthenRec k m n b
  strengthenRec k m n (TyEq a b) = TyEq <$> strengthenRec k m n a <*> strengthenRec k m n b
  strengthenRec k m n TmRefl = return TmRefl
  strengthenRec k m n (Subst a b) = Subst <$> strengthenRec k m n a <*> strengthenRec k m n b
  strengthenRec k m n (Contra a) = Contra <$> strengthenRec k m n a
  strengthenRec k m n TrustMe = pure TrustMe
  strengthenRec k m n PrintMe = pure PrintMe

instance Strengthen Match where
  strengthenRec k m n (Branch bnd) = Branch <$> strengthenRec k m n bnd

--------------------------------------------------------
-- Alpha equivalence (Eq type class)
--------------------------------------------------------

instance Eq (Term n) where
  (Pos _ a) == b = a == b
  a == Pos _ b = a == b
  TyType == TyType = True
  Lam b1 == Lam b2 = b1 == b2
  Var x == Var y = x == y
  Global x == Global y = x == y
  Pi a1 b1 == Pi a2 b2 = a1 == a2 && b1 == b2
  Let a1 b1 == Let a2 b2 = a1 == a2 && b1 == b2
  TyCon n1 a1 == TyCon n2 a2 = n1 == n2 && a1 == a2
  DataCon n1 a1 == DataCon n2 a2 = n1 == n2 && a1 == a2
  Case a1 b1 == Case a2 b2 = a1 == a2 && b1 == b2
  App a1 b1 == App a2 b2 = a1 == a2 && b1 == b2
  Ann a1 b1 == Ann a2 b2 = a1 == a2 && b1 == b2
  TyEq a1 b1 == TyEq a2 b2 = a1 == a2 && b1 == b2
  Subst a1 b1 == Subst a2 b2 = a1 == a2 && b1 == b2
  TmRefl == TmRefl = True
  Contra a == Contra b = a == b
  _ == _ = False

instance PatEq (Pattern p1) (Pattern p2) where
  patEq ::
    Pattern p1 ->
    Pattern p2 ->
    Maybe (Size (Pattern p1) :~: Size (Pattern p2))
  -- ignore local names
  patEq (PatVar _) (PatVar _) = Just Refl
  patEq (PatCon s1 ps1) (PatCon s2 ps2)
    | s1 == s2 =
        patEq ps1 ps2
  patEq _ _ = Nothing

instance Eq (Match n) where
  (Branch p1) == (Branch p2) =
    case patEq (Pat.getPat p1) (Pat.getPat p2) of
      Just Refl ->
        Pat.getBody p1 == Pat.getBody p2
      Nothing -> False

-- To compare pattern binders, we need to unbind, but also
-- make sure that the patterns are equal
instance (SNatI m, Eq (Term n)) => Eq (Pat.Bind Term Term (Pattern m) n) where
  b1 == b2 =
    Maybe.isJust (patEq (Pat.getPat b1) (Pat.getPat b2))
      && Pat.getBody b1 == Pat.getBody b2

-- To compare binders, we only need to `unbind` them
instance (Eq (Term n)) => Eq (Local.Bind Term Term n) where
  b1 == b2 = Local.getBody b1 == Local.getBody b2

-- With the instance above the derivable equality instance
-- is alpha-equivalence
-- deriving instance (Eq (Term n))

-------------------------------------------------------
-- Prelude datatypes
-------------------------------------------------------

sigmaDef :: DataDef
sigmaDef =
  DataDef
    { data_delta =
        LocalDecl @N0 (LocalName "A") TyType
          <:> LocalDecl @N1 (LocalName "B") (Pi (Var f0) (Local.bind (LocalName "x") TyType))
          <:> TNil,
      data_sort = TyType,
      data_constructors = [prodCon]
    }

prodCon :: ConstructorDef N2
prodCon =
  ConstructorDef
    { con_name = "Prod",
      con_theta =
        LocalDecl (LocalName "a") (Var f1)
          <:> LocalDecl
            (LocalName "b")
            (App (Var f1) (Var f0))
          <:> TNil
    }

unitDef :: DataDef
unitDef =
  DataDef
    { data_delta = TNil,
      data_sort = TyType,
      data_constructors = [unitCon]
    }

unitCon :: ConstructorDef N0
unitCon =
  ConstructorDef
    { con_name = "()",
      con_theta = TNil
    }

boolDef :: DataDef
boolDef =
  DataDef
    { data_delta = TNil,
      data_sort = TyType,
      data_constructors = [boolCon False, boolCon True]
    }

boolCon :: Bool -> ConstructorDef N0
boolCon b = ConstructorDef {con_name = show b, con_theta = TNil}

eitherDef :: DataDef
eitherDef =
  DataDef
    { data_delta =
        LocalDecl (LocalName "A") TyType
          <:> LocalDecl (LocalName "B") TyType
          <:> TNil,
      data_sort = TyType,
      data_constructors = [eitherLeft, eitherRight]
    }

eitherLeft :: ConstructorDef N2
eitherLeft =
  ConstructorDef
    { con_name = "Left",
      con_theta = LocalDecl (LocalName "a") (Var f0) <:> TNil
    }

eitherRight :: ConstructorDef N2
eitherRight =
  ConstructorDef
    { con_name = "Right",
      con_theta =
        LocalDecl (LocalName "b") (Var f1) <:> TNil
    }

prelude :: [ModuleEntry]
prelude =
  [ ModuleData "Unit" unitDef,
    ModuleData "Bool" boolDef,
    ModuleData "Either" eitherDef,
    ModuleData "Sigma" sigmaDef
  ]

initialConstructorNames :: ConstructorNames
initialConstructorNames =
  foldr g (ConstructorNames Set.empty Set.empty) prelude
  where
    g (ModuleData dn (DataDef _ _ dc)) cn =
      ConstructorNames
        { tconNames = Set.insert dn (tconNames cn),
          dconNames = Set.union (Set.fromList (map con_name dc)) (dconNames cn)
        }
    g _ cn = cn

--------------------------------------------------------
-- Show instances
--------------------------------------------------------

deriving instance (Show (Term n))

deriving instance (Show (Match n))

deriving instance (Show (Pattern p))

deriving instance (Show (Pat.PatList Pattern p))

instance Show (Pat.Bind Term Term (Pattern p) n) where
  show b = show (Pat.getPat b) ++ "=>" ++ show (Pat.getBody b)

instance Show (Local.Bind Term Term n) where
  show b = Local.unbind b $ \(x, body) -> show x ++ "." ++ show body
