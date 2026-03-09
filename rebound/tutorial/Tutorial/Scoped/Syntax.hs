{-|
Module      : Tutorial.Scoped.Syntax
Description : Well-scoped abstract syntax for a simply-typed lambda calculus
Copyright   : (c) Stephanie Weirich, 2026
License     : MIT
Maintainer  : sweirich@seas.upenn.edu
Stability   : experimental

A simply-typed lambda calculus with binary products and sums whose terms are
indexed by a 'Nat' tracking the number of free variables in scope.  Variable
occurrences are represented as 'Fin n' indices (de Bruijn style), and the
`rebound` library's 'Bind1' / 'Bind2' abstractions handle binding with
pretty-printing hints stored in 'LocalName' values.
-}
module Tutorial.Scoped.Syntax(Ty(..), Tm(..), module Rebound, module Data.LocalName, module Rebound.Bind.Local) where

import Rebound hiding (Ctx)
import Rebound.Bind.Local
import Data.LocalName

-- | Types of the simply-typed lambda calculus
data Ty
  -- | Unit type (terminal object)
  = One
  -- | Void type (initial object)
  | Zero
  -- | Function type
  | Ty :-> Ty
  -- | Binary product
  | Ty :* Ty
  -- | Binary sum (coproduct)
  | Ty :+ Ty
  deriving (Eq, Show)

--data Branch n where 
--    Branch :: forall m n. SNatI m => Pat.Bind Tm Tm (Pat m) (m + n) -> Branch n 

-- | Terms of the simply-typed lambda calculus, parameterised by the number of
-- free variables @n@ in scope.  Variable occurrences are de Bruijn indices
-- ('Fin n'); binders use 'Bind1' (one new variable) or 'Bind2' (two new
-- variables).
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

 