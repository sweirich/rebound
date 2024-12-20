module PiForall.ConcreteSyntax where

import Text.ParserCombinators.Parsec.Pos (SourcePos, newPos)
import Data.Maybe qualified as Maybe
import Data.Set (Set)
import Data.Set qualified as Set

import PiForall.Syntax (ConstructorNames)

-- | names of top level declarations/definitions
-- must be unique
type GlobalName = String

-- | names of type constructors, like 'list'
type TyConName = String

-- | names of data constructors, like 'cons'
type DataConName = String

type LocalName = String

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

-- | Patterns (without embedded type annotations)
-- `p` is the number of variables bound by the pattern
-- `n` is the number of free variables in type annotations in the pattern
-- LocalName is used for printing only, irrelevant for alpha-equivalence
data Pattern where
  PatCon :: DataConName -> [Pattern] -> Pattern 
  PatVar :: LocalName -> Pattern

-- A single branch in a match expression. Binds a pattern
-- with expression variables, with an expression body
data Match
  = Branch Pattern Term

-- | Local assumption
data Entry where
  EntryDecl :: String -> Typ -> Entry -- binding assumption
  EntryDef  :: String -> Term -> Entry -- nonbinding assumption

-- Telescopes: snoc-lists of variable assumptions x1:A1, x2:A2, ....,xp:Ap
-- That are used as typing contexts
-- 'p' is the number of variables introduced by the telescope
-- 'n' is the scope depth for A1 (and A2 has depth S n, etc.)
type Telescope = [Entry]
  
-- | add a new local entry to a telescope
(<:>) :: Telescope -> Entry -> Telescope
t <:> e = t ++ [e]

-- | Toplevel components of modules
data ModuleEntry
  = ModuleDecl { declName :: GlobalName, declType :: Typ }
  | ModuleDef  { declName :: GlobalName, declTerm :: Term }
  | ModuleData DataDef

-- | Datatype definitions
data DataDef = 
  DataDef
  { data_name :: TyConName,
    data_params :: Telescope,
    data_sort :: Typ,
    data_constructors :: [ConstructorDef]
  }

data ConstructorDef = 
  ConstructorDef
  { con_pos :: SourcePos,
    con_name :: DataConName,
    con_arguments :: Telescope 
  }

newtype ScopedConstructorDef = 
  ScopedConstructorDef (Telescope, ConstructorDef)

------------------------------------------------------------------

-- | module names
type ModuleName = String

-- | A Module has a name, a list of imports, a list of declarations,
--   and a set of constructor names (which affect parsing).
data Module = Module
  { moduleName :: ModuleName,
    moduleImports :: [ModuleImport],
    moduleEntries :: [ModuleEntry],
    moduleConstructors :: ConstructorNames
  }

-- | References to other modules (brings declarations and definitions into scope)
newtype ModuleImport = ModuleImport ModuleName


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



