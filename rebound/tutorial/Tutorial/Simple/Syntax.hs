{-|
Module      : Simple.Syntax
Description : Abstract syntax for simply typed language, uses rebound
Copyright   : (c) Stephanie Weirich, 2026
License     : MIT
Maintainer  : sweirich@seas.upenn.edu
Stability   : experimental

A simply-typed lambda calculus with binary products and sums. Demonstrates a 
simple use of the `rebound` library.

-}
module Tutorial.Simple.Syntax(Ty(..), Tm(..), module Rebound, module Rebound.Bind.PatN) where

import Rebound
import Rebound.Bind.PatN 

-- Types 
data Ty = One | Zero | Ty :-> Ty | Ty :* Ty | Ty :+ Ty 
  deriving (Eq, Show)

data Branch n where 
    Branch :: forall m n. SNatI m => Pat.Bind Tm Tm (Pat m) (m + n) -> Branch n 

-- Terms 
data Tm (n :: Nat) where
    -- variable
    Var   :: Fin n -> Tm n
    -- values
    Lam   :: Bind1 Tm Tm n -> Tm n
    Unit  :: Tm n
    Pair  :: Tm n -> Tm n -> Tm n
    Inj   :: Int -> Tm n -> Tm n
    -- elimination forms for functions (negative values)
    App       :: Tm n -> Tm n -> Tm n
    -- elimination forms for positive values
    MatchUnit :: Tm n -> Tm n -> Tm n
    MatchPair :: Tm n -> Bind2 Tm Tm n -> Tm n
    MatchSum  :: Tm n -> Bind1 Tm Tm n -> Bind1 Tm Tm n -> Tm n
    -- type annotation

    Ann  :: Tm n -> Ty -> Tm n
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

 