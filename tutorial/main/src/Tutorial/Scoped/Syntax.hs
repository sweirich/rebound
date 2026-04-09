{-|
Module      : Tutorial.Scoped.Syntax
Description : Well-scoped abstract syntax for a simply-typed lambda calculus

A simply-typed lambda calculus with binary products and sums whose terms are
indexed by a 'Nat' tracking the number of free variables in scope.  Variable
occurrences are represented as 'Fin' n indices (de Bruijn style), and the
`rebound` library's 'Bind1' / 'Bind2' abstractions handle binding with
pretty-printing hints stored in 'LocalName' values.
-}
module Tutorial.Scoped.Syntax(
    Ty(..), Tm(..), 
    tmSize, maxScope, height,
    module Rebound, 
    module Rebound.Bind.Local) where

import Rebound hiding (Ctx)
import Rebound.Bind.Local
import Data.Fin

data Ty = One | Ty :-> Ty | Ty :* Ty | Ty :+ Ty
  deriving (Eq, Show)


data Tm (n :: Nat) where
    Var   :: Fin n -> Tm n
    Lam   :: Bind1 Tm Tm n -> Tm n
    Unit  :: Tm n
    Pair  :: Tm n -> Tm n -> Tm n
    Inj   :: Int -> Tm n -> Tm n
    -- application `e0 e1`
    App       :: Tm n -> Tm n -> Tm n
    -- simple pattern matching
    -- `case e0 of () -> e1`
    MatchUnit :: Tm n -> Tm n -> Tm n
    -- `case e0 of (x,y) -> e1`
    MatchPair :: Tm n -> Bind2 Tm Tm n -> Tm n
    -- `case e0 of {inj1 x -> e1 ; inj2 y -> e2 }`
    MatchSum  :: Tm n -> Bind1 Tm Tm n -> Bind1 Tm Tm n -> Tm n
      deriving (Generic1, Eq, Show)

--------------------------------------------------------------------
-- Automatic derivation of substitution
--------------------------------------------------------------------

instance SubstVar Tm where
  var :: Fin n -> Tm n
  var = Var
instance Subst Tm Tm where
  isVar :: Tm n -> Maybe (Tm :~: Tm, Fin n)
  isVar (Var x) = Just (Refl, x)
  isVar _ = Nothing

{-
  applyE r (Var x) = applyEnv r x
  applyE r (App e1 e2) = App (applyE r e1) (applyE r e2)
  applyE r (Lam b) = Lam (applyE r b)
  applyE r Unit = Unit
-}  

-- >>> :info Subst
-- type Subst :: (Nat -> *) -> (Nat -> *) -> Constraint
-- class SubstVar v => Subst v c where
--   applyE :: Env v n m -> c n -> c m
--   default applyE :: (Generic1 c, GSubst v (Rep1 c), SubstVar v) =>
--                     Env v m n -> c m -> c n
--   isVar :: c n -> Maybe (v :~: c, Fin n)
--   	-- Defined in ‘Rebound.Env.Lazy’
-- instance Subst Tm Tm
--   -- Defined at /Users/sweirich/github/haskell/rebound/tutorial/main/src/Tutorial/Scoped/Syntax.hs:49:10
-- instance [overlap ok] Subst Fin Fin -- Defined in ‘Rebound.Env’
-- instance [overlappable] SubstVar v => Subst v Fin
--   -- Defined in ‘Rebound.Env’


-- >>> applyE (Unit .: zeroE) (Var FZ)
-- Unit


-- >>> applyE (Unit .: zeroE) (Lam (bind1 (LocalName "x") (Var f1)))
-- Lam (bind1 (Unit))


-- >>> Lam (bind1 (LocalName "x") (Var f0))
-- Lam (bind1 (Var 0))

--------------------------------------------------------------------
-- Show instances for Bind1/Bind2
--------------------------------------------------------------------

instance Show (Bind1 Tm Tm n) where
    show bnd = "(bind1 (" ++ show (getBody1 bnd) ++ "))"
instance Show (Bind2 Tm Tm n) where
    show bnd = "(bind2 (" ++ show (getBody2 bnd) ++ "))"


--------------------------------------------------------------------
-- Additional functions on syntax
--------------------------------------------------------------------
-- | Count the number of nodes in an AST
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

-- | Determine the length of the longest path
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
