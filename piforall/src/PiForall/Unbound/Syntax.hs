{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}

-- | The abstract syntax of the simple dependently typed language
-- See the comment at the top of 'Parser' for the concrete syntax of this language
module PiForall.Unbound.Syntax
  ( module PiForall.Unbound.Syntax,
    GlobalName,
    ConstructorNames (..),
    TyConName (..),
    DataConName (..),
    ModuleImport (..),
    ModuleName (..),
  )
where

import Data.Function (on)
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Typeable (Typeable)
import GHC.Base (MonadPlus)
import GHC.Generics (Generic, from)
import PiForall.ConcreteSyntax (ConstructorNames (..), DataConName, GlobalName, ModuleImport (..), ModuleName, TyConName)
import Text.ParserCombinators.Parsec.Pos (SourcePos, initialPos, newPos)
import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold qualified as Unbound

-----------------------------------------

-- * Names

-----------------------------------------

-- | For variable names, we use the `Unbound` library to
-- automatically generate free variable, substitution,
-- and alpha-equality function. The abstract type `Name` from
-- this library is indexed by the AST type that this variable
-- is a name for.
type TName = Unbound.Name Term

-----------------------------------------

-- * Core language of pi-forall (Combined syntax for types and terms)

-----------------------------------------

-- | Because types and terms use the same AST, we define the following
-- type synonym so that we can hint whether a piece of syntax is being used
-- as a type or as a term.
type Type = Term

-- | basic language
data Term
  = -- | type of types, concretely `Type`
    TyType
  | -- | variable `x`
    Var TName
  | -- | abstraction  `\x. a`
    Lam Epsilon (Unbound.Bind TName Term)
  | -- | application `a b`
    App Term Arg
  | -- | function type   `(x : A) -> B`
    TyPi Epsilon Type (Unbound.Bind TName Type)
  | -- | annotated terms `( a : A )`
    Ann Term Type
  | -- | marked source position, for error messages
    Pos SourcePos Term
  | -- | an axiom 'TRUSTME', inhabits all types
    TrustMe
  | -- | a directive to the type checker to print out the current context
    PrintMe
  | -- | let expression, introduces a new (non-recursive) definition in the ctx
    -- | `let x = a in b`
    Let Term (Unbound.Bind TName Term)
  | -- | Equality type  `a = b`
    TyEq Term Term
  | -- | Proof of equality `Refl`
    Refl
  | -- | equality type elimination  `subst a by pf`
    Subst Term Term
  | -- | witness to an equality contradiction
    Contra Term
  | -- | type constructors (fully applied)
    TyCon TyConName [Arg]
  | -- | term constructors (fully applied)
    DataCon DataConName [Arg]
  | -- | case analysis  `case a of matches`
    Case Term [Match]
  deriving (Show, Generic)

-- | An argument to a function
data Arg = Arg {argEp :: Epsilon, unArg :: Term}
  deriving (Show, Generic, Unbound.Alpha, Unbound.Subst Term)

-- | Epsilon annotates the stage of a variable
data Epsilon
  = Rel
  | Irr
  deriving
    ( Eq,
      Show,
      Read,
      Bounded,
      Enum,
      Ord,
      Generic,
      Unbound.Alpha,
      Unbound.Subst Term
    )

-- | A 'Match' represents a case alternative
newtype Match = Match (Unbound.Bind Pattern Term)
  deriving (Show, Generic, Typeable)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

-- | The patterns of case expressions bind all variables
-- in their respective branches.
data Pattern
  = PatCon DataConName [(Pattern, Epsilon)]
  | PatVar TName
  deriving (Show, Eq, Generic, Typeable, Unbound.Alpha, Unbound.Subst Term)

-----------------------------------------

-- * Modules and declarations

-----------------------------------------

-- | A Module has a name, a list of imports, a list of declarations,
--   and a set of constructor names (which affect parsing).
data Module = Module
  { moduleName :: ModuleName,
    moduleImports :: [ModuleImport],
    moduleEntries :: [ModuleEntry],
    moduleConstructors :: ConstructorNames
  }
  deriving (Show, Generic, Typeable, Unbound.Alpha)

-- | A type declaration
data TypeDecl = TypeDecl {declName :: TName, declEp :: Epsilon, declType :: Type}
  deriving (Show, Generic, Typeable, Unbound.Alpha, Unbound.Subst Term)

-- | Declare the type of a term
mkDecl :: TName -> Type -> Entry
mkDecl n ty = Decl (TypeDecl n Rel ty)

data Entry
  = -- | Declaration for the type of a term  'x : A'
    Decl TypeDecl
  | -- | The definition of a particular name 'x = a'
    -- must already have a type declaration in scope
    Def TName Term
  deriving (Show, Generic, Typeable)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

-- | Entries are the components of modules
data ModuleEntry
  = -- | Declaration for the type of a term  'x : A'
    ModuleDecl TypeDecl
  | -- | The definition of a particular name 'x = a'
    -- must already have a type declaration in scope
    ModuleDef TName Term
  | -- | Datatype definition (must be at the module level)
    ModuleData TyConName Telescope [ConstructorDef]
  | Demote Epsilon
  deriving (Show, Generic, Typeable)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

promote :: Entry -> ModuleEntry
promote (Decl t) = ModuleDecl t
promote (Def n t) = ModuleDef n t

-----------------------------------------

-- * Datatypes

-----------------------------------------

-- | A Data constructor has a name and a telescope of arguments
data ConstructorDef = ConstructorDef SourcePos DataConName Telescope
  deriving (Show, Generic)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

-- ** Telescopes

-- | A telescope is like a first class context. It is a list of
-- assumptions, binding each variable in terms that appear
-- later in the list.
-- For example
--     Delta = [ x:Type , y:x, y = w ]
newtype Telescope = Telescope [Entry]
  deriving (Show, Generic)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

-----------------------------------------
-- Definitions related to datatypes

-- | Is this the syntax of a literal (natural) number
isNumeral :: Term -> Maybe Int
isNumeral (Pos _ t) = isNumeral t
isNumeral (DataCon c []) | c == "Zero" = Just 0
isNumeral (DataCon c [Arg _ t]) | c == "Succ" =
  do n <- isNumeral t; return (n + 1)
isNumeral _ = Nothing

-- | Is this pattern a variable
isPatVar :: Pattern -> Bool
isPatVar (PatVar _) = True
isPatVar _ = False

-- | built-in set of constructor names
initialConstructorNames :: ConstructorNames
initialConstructorNames = ConstructorNames initialTCNames initialDCNames

-- | prelude names for built-in datatypes
sigmaName :: TyConName
sigmaName = "Sigma"

prodName :: DataConName
prodName = "Prod"

boolName :: TyConName
boolName = "Bool"

trueName :: DataConName
trueName = "True"

falseName :: DataConName
falseName = "False"

tyUnitName :: TyConName
tyUnitName = "Unit"

litUnitName :: DataConName
litUnitName = "()"

initialTCNames :: Set TyConName
initialTCNames = Set.fromList [sigmaName, boolName, tyUnitName]

initialDCNames :: Set DataConName
initialDCNames = Set.fromList [prodName, trueName, falseName, litUnitName]

preludeDataDecls :: [ModuleEntry]
preludeDataDecls =
  [ ModuleData sigmaName sigmaTele [prodConstructorDef],
    ModuleData tyUnitName (Telescope []) [unitConstructorDef],
    ModuleData boolName (Telescope []) [falseConstructorDef, trueConstructorDef]
  ]
  where
    -- boolean
    trueConstructorDef = ConstructorDef internalPos trueName (Telescope [])
    falseConstructorDef = ConstructorDef internalPos falseName (Telescope [])

    -- unit
    unitConstructorDef = ConstructorDef internalPos litUnitName (Telescope [])

    -- Sigma-type
    sigmaTele = Telescope [declA, declB]
    prodConstructorDef = ConstructorDef internalPos prodName (Telescope [declX, declY])
    declA = mkDecl aName TyType
    declB = mkDecl bName (TyPi Rel (Var aName) (Unbound.bind xName TyType))
    declX = mkDecl xName (Var aName)
    declY = mkDecl yName (App (Var bName) (Arg Rel (Var xName)))
    aName = Unbound.string2Name "a"
    bName = Unbound.string2Name "b"

    internalPos :: SourcePos
    internalPos = initialPos "prelude"

-----------------------------------------

-- * Auxiliary functions on syntax

-----------------------------------------

-- | Remove source positions and type annotations from the top level of a term
strip :: Term -> Term
strip (Pos _ tm) = strip tm
strip (Ann tm _) = strip tm
strip tm = tm

-- | Partial inverse of Pos
unPos :: Term -> Maybe SourcePos
unPos (Pos p _) = Just p
unPos _ = Nothing

-- | Tries to find a Pos inside a term, otherwise just gives up.
unPosFlaky :: Term -> SourcePos
unPosFlaky t = fromMaybe (newPos "unknown location" 0 0) (unPos t)

-----------------------------------------

-- * Unbound library

-----------------------------------------

-- We use the unbound-generics library to mark the binding occurrences of
-- variables in the syntax. That allows us to automatically derive
-- functions for alpha-equivalence, free variables and substitution
-- using generic programming.

-- The definitions below specialize the generic operations from the libary
-- to some of the common uses that we need in pi-forall

-- | Determine when two terms are alpha-equivalent (see below)
aeq :: Term -> Term -> Bool
aeq = Unbound.aeq

-- | Calculate the free variables of a term
fv :: Term -> [Unbound.Name Term]
fv = Unbound.toListOf Unbound.fv

-- | in a binder `x.a` replace `x` with `b`
instantiate :: Unbound.Bind TName Term -> Term -> Term
instantiate bnd a = Unbound.substBind bnd a

-- | in a binder `x.a` replace `x` with a fresh name
unbind :: (Unbound.Fresh m) => Unbound.Bind TName Term -> m (TName, Term)
unbind = Unbound.unbind

-- | in binders `x.a1` and `x.a2` replace `x` with a fresh name in both terms
unbind2 :: (Unbound.Fresh m) => Unbound.Bind TName Term -> Unbound.Bind TName Term -> m (TName, Term, Term)
unbind2 b1 b2 = do
  o <- Unbound.unbind2 b1 b2
  case o of
    Just (x, t, _, u) -> return (x, t, u)
    Nothing -> error "impossible"

------------------

-- * `Alpha` class instances

-- The Unbound library's `Alpha` class enables the `aeq`, `fv`,
-- `instantiate` and `unbind` functions, and also allows some
-- specialization of their generic behavior.

-- For `Term`, we'd like Alpha equivalence to ignore
-- source positions and type annotations. So we make sure to
-- remove them before calling the generic operation.

instance Unbound.Alpha Term where
  aeq' :: Unbound.AlphaCtx -> Term -> Term -> Bool
  aeq' ctx a b = (Unbound.gaeq ctx `on` from) (strip a) (strip b)

-- For example, all occurrences of annotations and source positions
-- are ignored by this definition.

-- '(Bool : Type)' is alpha-equivalent to 'Bool'
-- >>> aeq (Ann TyBool TyType) TyBool

-- '(Bool, Bool:Type)' is alpha-equivalent to (Bool, Bool)
-- >>> aeq (Prod TyBool (Ann TyBool TyType)) (Prod TyBool TyBool)

-- At the same time, the generic operation equates terms that differ only
-- in the names of bound variables.

-- 'x'
xName :: TName
xName = Unbound.string2Name "x"

-- 'y'
yName :: TName
yName = Unbound.string2Name "y"

-- '\x -> x`
idx :: Term
idx = Lam Rel (Unbound.bind xName (Var xName))

-- '\y -> y`
idy :: Term
idy = Lam Rel (Unbound.bind yName (Var yName))

-- >>> aeq idx idy

---------------

-- * Substitution

-- The Subst class derives capture-avoiding substitution.
-- It has two parameters because the type of thing we are substituting
-- for may not be the same as what we are substituting into.

-- The `isvar` function identifies the variables in the term that
-- should be substituted for.
instance Unbound.Subst Term Term where
  isvar (Var x) = Just (Unbound.SubstName x)
  isvar _ = Nothing

-- '(y : x) -> y'
pi1 :: Term
pi1 = TyPi Rel (Var xName) (Unbound.bind yName (Var yName))

-- >>> Unbound.aeq (Unbound.subst xName TyBool pi1) pi2

-----------------

-- Substitutions ignore source positions
instance Unbound.Subst b SourcePos where
  subst _ _ = id
  substs _ = id
  substBvs _ _ = id
