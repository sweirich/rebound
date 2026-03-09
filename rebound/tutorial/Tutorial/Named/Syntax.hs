{-|
Module      : Tutorial.Named.Syntax
Description : Abstract syntax of typed lambda calclus with names

This module defines the abstract syntax for a simple typed
lambda calculus with n-ary products and sums.

Both products and sums are eliminated via pattern 
matching. This syntax is used for parsing and pretty 
printing. The `Named.Parser` module contains a description 
of a concrete syntax for this language, and the Named.PP
module converts this abstract representation into the 
concrete syntax.

-}

module Tutorial.Named.Syntax(
  Ty(..),
  Tm(..),

  -- $syntactic sugar
  letTm,
  voidTy, 
  voidElim, 
  unitTy, 
  unitTm,
  boolTy, 
  falseTm, 
  trueTm, 
  ifTm
)
where

-- | Types 
data Ty 
  -- | function type
  = Ty :-> Ty 
  -- | n-ary product
  | Prod [Ty] 
  -- | n-ary sum
  | Sum [Ty]
  deriving (Show, Eq)

-- make arrow type constructor right associative
infixr 0 :->

-- | Terms
data Tm where
    -- | variable
    Var   :: String -> Tm
    -- | λ term
    Lam   :: String -> Tm -> Tm
    -- | application
    App   :: Tm -> Tm -> Tm
    -- | tuples (e1, ..., en)
    Pair  :: [ Tm ] -> Tm
    -- | Inj i e
    Inj   :: Int -> Tm -> Tm
    -- | Case analysis with list of pattern,branches
    Case  :: Tm -> [(Tm,Tm)] -> Tm
      deriving (Show, Eq)

-- * Syntactic sugar
--
-- $syntacticSugar
--
-- We can make this language slightly more expressive by 
-- including standard definitions for void, unit and boolean
-- types.

-- | Let term  "let x = e1 in e2"
letTm :: String -> Tm -> Tm -> Tm
letTm x rhs body = App (Lam x body) rhs

-- | Void type (0) -- the empty sum
voidTy :: Ty
voidTy = Sum []

-- | Elimination form for Void, no branches needed
voidElim :: Tm -> Tm 
voidElim e = Case e []

-- | Unit type (1) -- the empty product
unitTy :: Ty
unitTy = Prod []

-- | Unit value ()
unitTm :: Tm 
unitTm = Pair []

-- | Bool type (2) -- represented as Unit + Unit
boolTy :: Ty
boolTy = Sum [unitTy, unitTy]

-- | False value
falseTm :: Tm
falseTm = Inj 0 unitTm

-- | True value
trueTm :: Tm
trueTm = Inj 1 unitTm

-- | If expression
ifTm :: Tm -> Tm -> Tm -> Tm
ifTm cond tru fls = Case cond [(falseTm, fls), (trueTm, tru)]
