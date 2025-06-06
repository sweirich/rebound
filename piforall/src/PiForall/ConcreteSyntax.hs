{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveAnyClass #-}
module PiForall.ConcreteSyntax where

import Data.LocalName
import Data.Maybe qualified as Maybe
import Data.Set (Set)
import Data.Set qualified as Set
import Text.ParserCombinators.Parsec.Pos (SourcePos, newPos)

-- For the unbound version
import GHC.Generics (Generic,from)
import Unbound.Generics.LocallyNameless qualified as Unbound
import Data.Typeable (Typeable)


-- | names of top level declarations/definitions
-- must be unique
type GlobalName = String

-- | names of type constructors, like 'list'
type TyConName = String

-- | names of data constructors, like 'cons'
type DataConName = String

-- | The names of all type/data constructors used in the module
data ConstructorNames = ConstructorNames
  { tconNames :: Set.Set TyConName,
    dconNames :: Set.Set DataConName
  }
  deriving (Show, Generic, Typeable, Eq)

type Typ = Term

data Term
  = TyType
  | Lam LocalName Term
  | Var LocalName
  | Global GlobalName
  | Pi Typ LocalName Term
  | Pos SourcePos Term
  | Let LocalName Term Term
  | TyCon TyConName [Typ]
  | DataCon DataConName [Term]
  | Case Term [Match]
  | App Term Term
  | Ann Term Typ
  | TyEq Term Term
  | Subst Term Term
  | TmRefl
  | Contra Term
  | TrustMe
  | PrintMe
  deriving (Eq, Show)

-- | Patterns (without embedded type annotations)
-- `p` is the number of variables bound by the pattern
-- `n` is the number of free variables in type annotations in the pattern
-- LocalName is used for printing only, irrelevant for alpha-equivalence
data Pattern where
  PatCon :: DataConName -> [Pattern] -> Pattern
  PatVar :: LocalName -> Pattern
  deriving (Eq, Show)

-- A single branch in a match expression. Binds a pattern
-- with expression variables, with an expression body
data Match
  = Branch Pattern Term
  deriving (Eq, Show)

-- | Local assumption
data Entry where
  EntryDecl :: LocalName -> Typ -> Entry -- binding assumption
  EntryDef :: LocalName -> Term -> Entry -- nonbinding assumption

-- Telescopes: snoc-lists of variable assumptions x1:A1, x2:A2, ....,xp:Ap
-- That are used as typing contexts
-- 'p' is the number of variables introduced by the telescope
-- 'n' is the scope depth for A1 (and A2 has depth S n, etc.)
newtype Telescope = Telescope [Entry]

-- | add a new local entry to a telescope
(<:>) :: Telescope -> Entry -> Telescope
Telescope t <:> e = Telescope $ t ++ [e]

-- | Toplevel components of modules
data ModuleEntry
  = ModuleDecl {declName :: GlobalName, declType :: Typ}
  | ModuleDef {declName :: GlobalName, declTerm :: Term}
  | ModuleData {declName :: GlobalName, declData :: DataDef}
  | ModuleFail {failing :: ModuleEntry}

-- | Datatype definitions
data DataDef = DataDef
  { data_params :: Telescope,
    data_sort :: Typ,
    data_constructors :: [ConstructorDef]
  }

data ConstructorDef = ConstructorDef
  { con_pos :: Maybe SourcePos,
    con_name :: DataConName,
    con_arguments :: Telescope
  }

newtype ScopedConstructorDef
  = ScopedConstructorDef (Telescope, ConstructorDef)

------------------------------------------------------------------

-- | module names
type ModuleName = String

-- | References to other modules (brings their declarations and
-- definitions into the global scope)
newtype ModuleImport = ModuleImport ModuleName
  deriving (Show, Eq, Ord, Generic, Typeable)
  deriving anyclass (Unbound.Alpha)

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
isNumeral :: Term -> Maybe Int
isNumeral (Pos _ t) = isNumeral t
isNumeral (DataCon c []) | c == "Zero" = Just 0
isNumeral (DataCon c [t]) | c == "Succ" =
  do n <- isNumeral t; return (n + 1)
isNumeral _ = Nothing

-- | Is this pattern a variable
isPatVar :: Pattern -> Bool
isPatVar (PatVar _) = True
isPatVar _ = False

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
unPosFlaky t = Maybe.fromMaybe (newPos "unknown location" 0 0) (unPos t)

-------------------------------------------------------
-- Prelude datatypes
-------------------------------------------------------

initialConstructorNames :: ConstructorNames
initialConstructorNames =
  ConstructorNames
    { tconNames = Set.fromList ["Unit", "Bool", "Either", "Sigma"],
      dconNames = Set.fromList ["()", "True", "False", "Left", "Right", "Prod"]
    }

-------------------------------------------------------
-- Prelude datatypes
-------------------------------------------------------

-- * Source Positions

-- SourcePositions do not have an instance of the Generic class available
-- so we cannot automatically define their `Alpha` and `Subst` instances.
-- Instead we provide a trivial implementation here.
instance Unbound.Alpha SourcePos where
  aeq' _ _ _ = True
  fvAny' _ _ = pure
  open _ _ = id
  close _ _ = id
  isPat _ = mempty
  isTerm _ = mempty
  nthPatFind _ = mempty
  namePatFind _ = mempty
  swaps' _ _ = id
  freshen' _ x = return (x, mempty)
  lfreshen' _ x cont = cont x mempty
  acompare' _ _ _ = EQ


-- * Constructor Names

-- ConstructorNames are sets, so they also do not have an instance of the
-- Generic class available so we cannot automatically define their
-- Alpha and Subst instances.
instance Unbound.Alpha ConstructorNames where
  aeq' _ a1 a2 = a1 == a2
  fvAny' _ _ = pure
  open _ _ = id
  close _ _ = id
  isPat _ = mempty
  isTerm _ = mempty
  nthPatFind _ = mempty
  namePatFind _ = mempty
  swaps' _ _ = id
  freshen' _ x = return (x, mempty)
  lfreshen' _ x cont = cont x mempty
  acompare' _ _ _ = EQ

