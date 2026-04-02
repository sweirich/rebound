{-|
Module      : Tutorial.Scoped.Syntax
Description : Well-scoped abstract syntax for a simply-typed lambda calculus

A simply-typed lambda calculus with binary products and sums whose terms are
indexed by a 'Nat' tracking the number of free variables in scope.  Variable
occurrences are represented as 'Fin n' indices (de Bruijn style), and the
`rebound` library's 'Bind1' / 'Bind2' abstractions handle binding with
pretty-printing hints stored in 'LocalName' values.
-}
module Tutorial.Scoped.Syntax(
    Ty(..), Tm(..), 
    -- tmSize, maxScope, height,
    module Rebound, 
    module Rebound.Bind.Local) where

import Rebound hiding (Ctx)
import Rebound.Bind.Local

-- | Types of the simply-typed lambda calculus
data Ty
  -- | Unit type (terminal object)
  = One
  -- | Function type
  | Ty :-> Ty
  -- | Binary product
  | Ty :* Ty
  -- | Binary sum (coproduct)
  | Ty :+ Ty
  deriving (Eq, Show)


-- | Terms of the simply-typed lambda calculus, indexed by the number of
-- free variables @n@ in scope.  
data Tm (n :: Nat) where
    -- | Variable occurrence — a de Bruijn index into scope @n@
    Var   :: Fin n -> Tm n
    -- | Lambda abstraction — binds one variable
    Lam   :: Bind1 Tm Tm n -> Tm n
    -- | Unit value @()@
    Unit  :: Tm n
    -- | Binary pair @(e1, e2)@
    Pair  :: Tm n -> Tm n -> Tm n
    -- | Injection into a sum: @Inj 0 e@ or @Inj 1 e@
    Inj   :: Int -> Tm n -> Tm n
    -- | Function application
    App       :: Tm n -> Tm n -> Tm n
    -- | Unit elimination — match scrutinee against @()@, then evaluate body
    MatchUnit :: Tm n -> Tm n -> Tm n
    -- | Pair elimination — bind both components in body
    MatchPair :: Tm n -> Bind2 Tm Tm n -> Tm n
    -- | Sum elimination — one branch for each injection, each binding its payload
    MatchSum  :: Tm n -> Bind1 Tm Tm n -> Bind1 Tm Tm n -> Tm n
      deriving (Generic1, Eq, Show)

instance Show (Bind1 Tm Tm n) where
    show bnd = "(bind1 (" ++ show (getBody1 bnd) ++ "))"
instance Show (Bind2 Tm Tm n) where
    show bnd = "(bind2 (" ++ show (getBody2 bnd) ++ "))"

instance SubstVar Tm where
    var = Var
instance Subst Tm Tm where
  isVar (Var x) = Just (Refl, x)
  isVar _ = Nothing

{-
tmSize :: Tm n -> Int
tmSize (Var x)            = 1
tmSize (Lam b)            = 1 + tmSize (getBody1 b)
tmSize Unit               = 1
tmSize (Pair e1 e2)       = 1 + tmSize e1 + tmSize e2
tmSize (Inj _ e)          = 1 + tmSize e
tmSize (App e1 e2)        = 1 + tmSize e1 + tmSize e2
tmSize (MatchUnit e1 e2)  = 1 + tmSize e1 + tmSize e2
tmSize (MatchPair e b)    = 1 + tmSize e + tmSize (getBody2 b)
tmSize (MatchSum e b1 b2) = 1 + tmSize e + tmSize (getBody1 b1) + tmSize (getBody1 b2)

-- | Maximum number of binders enclosing any subterm, relative to the root.
-- Equivalently, the deepest binder nesting depth in the term.
maxScope :: Tm n -> Int
maxScope (Var _)            = 0
maxScope (Lam b)            = 1 + maxScope (getBody1 b)
maxScope Unit               = 0
maxScope (Pair e1 e2)       = max (maxScope e1) (maxScope e2)
maxScope (Inj _ e)          = maxScope e
maxScope (App e1 e2)        = max (maxScope e1) (maxScope e2)
maxScope (MatchUnit e1 e2)  = max (maxScope e1) (maxScope e2)
maxScope (MatchPair e b)    = max (maxScope e) (2 + maxScope (getBody2 b))
maxScope (MatchSum e b1 b2) = maximum [maxScope e, 1 + maxScope (getBody1 b1), 1 + maxScope (getBody1 b2)]

height :: Tm n -> Int
height (Var x)            = 1
height (Lam b)            = 1 + height (getBody1 b)
height Unit               = 1
height (Pair e1 e2)       = 1 + max (height e1) (height e2)
height (Inj _ e)          = 1 + height e
height (App e1 e2)        = 1 + max (height e1) (height e2)
height (MatchUnit e1 e2)  = 1 + max (height e1) (height e2)
height (MatchPair e b)    = 1 + max (height e) (height (getBody2 b))
height (MatchSum e b1 b2) = 1 + maximum [height e, height (getBody1 b1), height (getBody1 b2)]
-}