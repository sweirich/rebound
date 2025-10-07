{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}

-- |
-- Module      : Rebound.Env
-- Description : Environments, or mappings from variables to terms
--
-- Environments, also called _parallel substitutions_ or _multi-substitutions_,
-- map all variables in a scope to terms in another scope.


module Rebound.Env
  ( Env,
    applyEnv,
    SubstVar (..),
    Subst (..),
    Shiftable (..),
    GSubst (..),
    gapplyE,
    applyOpt,
    transform,
    zeroE,
    oneE,
    singletonE,
    idE,
    (.>>),
    (.:),
    (.++),
    head,
    tail,
    appendE,
    up,
    upN,
    shift1E,
    shiftNE,
    fromVec,
    toVec,
    tabulate,
    fromTable,
    weakenE',
    weakenER,
    shiftFromApplyE,
  )
where

-- The concrete implementation of environments can be changed by replacing
-- this import with an alternative one.
import Rebound.Env.Lazy

import Rebound.Classes (Shiftable (..))
import Rebound.Lib
import Control.Monad
import Data.Scoped.List (List, pattern Nil, pattern (:<))

import Data.Fin qualified as Fin
import Data.Map qualified as Map
import Data.Vec qualified as Vec
import GHC.Generics hiding (S)
import Prelude hiding (head, tail)

----------------------------------------------
-- operations on environments/substitutions
----------------------------------------------

-- | Convert a function into an environment.
env :: forall m v n. (SubstVar v, SNatI m) => (Fin m -> v n) -> Env v m n
env f = fromVec v
  where
    v :: Vec m (v n)
    v = Vec.tabulate f

-- | A singleton environment (single index domain),
-- which maps that single variable to the provided term.
oneE :: (SubstVar v) => v n -> Env v (S Z) n
oneE v = v .: zeroE

-- | An environment that maps index 0 to the provided term, and maps
-- all other indices to themselves.
singletonE :: (SubstVar v) => v n -> Env v (S n) n
singletonE v = v .: idE

-- | An identity environment, which maps all indices to themselves.
idE :: (SubstVar v) => Env v n n
idE = shiftNE s0

-- | Append two environments.
--
-- The `SNatI` constraint is a runtime witness for the length
-- of the domain of the first environment.
(.++) ::
  (SNatI p, SubstVar v) =>
  Env v p n ->
  Env v m n ->
  Env v (p + m) n
(.++) = appendE snat
-- By using a class constraint, this can be an infix operation.

-- | Append two environments, with the length @SNat p@ explicitly required.
--
-- If the length is implicitly available, '.++' might be preferable.
appendE ::
  (SubstVar v) =>
  SNat p ->
  Env v p n ->
  Env v m n ->
  Env v (p + m) n
appendE SZ e1 e2 = e2
appendE (snat_ -> SS_ p1) e1 e2 =
  head e1 .: appendE p1 (tail e1) e2

newtype AppendE v m n p = MkAppendE
  { getAppendE ::
      Env v p n ->
      Env v m n ->
      Env v (p + m) n
  }

-- | Access the term at index 0.
head :: (SubstVar v) => Env v (S n) m -> v m
head f = applyEnv f FZ

-- | Increment all free variables in image by 1.
shift1E :: (SubstVar v) => Env v n (S n)
shift1E = shiftNE s1

-- | Increment all free variables by @p@.
upN ::
  forall v p m n.
  (Subst v v) =>
  SNat p ->
  Env v m n ->
  Env v (p + m) (p + n)
upN p = getUpN @_ @_ @_ @p (withSNat p (induction base step))
  where
    base :: UpN v m n Z
    base = MkUpN id
    step :: forall p1. UpN v m n p1 -> UpN v m n (S p1)
    step (MkUpN r) = MkUpN $
      \e -> var Fin.f0 .: (r e .>> shiftNE s1)

newtype UpN v m n p = MkUpN {getUpN :: Env v m n -> Env v (p + m) (p + n)}

-- | Allow to implement 'Shiftable' using 'Subst'.
shiftFromApplyE :: forall v c k n. (SubstVar v, Subst v c) => SNat k -> c n -> c (k + n)
shiftFromApplyE k = applyE @v (shiftNE k)

----------------------------------------------------
-- Create an environment from a length-indexed
-- vector of scoped values

-- | Convert an environment to a 'Vec'.
fromVec :: (SubstVar v) => Vec m (v n) -> Env v m n
fromVec VNil = zeroE
fromVec (x ::: vs) = x .: fromVec vs

-- | Convert a 'Vec' to an environment.
toVec :: (SubstVar v) => SNat m -> Env v m n -> Vec m (v n)
toVec SZ r = VNil
toVec m@(snat_ -> SS_ m') r = head r ::: toVec m' (tail r)

----------------------------------------------------------------
-- show for environments
----------------------------------------------------------------

instance (SNatI n, Show (v m), SubstVar v) => Show (Env v n m) where
  show x = show (tabulate x)

-- | Convert an environment to an association list.
tabulate :: (SNatI n, Subst v v) => Env v n m -> [(Fin n, v m)]
tabulate r = map (\f -> (f, applyEnv r f)) Fin.universe

-- | Convert an association list to an environment.
fromTable ::
  forall n v.
  (SNatI n, SubstVar v) =>
  [(Fin n, v n)] ->
  Env v n n
fromTable rho =
  env $ \f -> case lookup f rho of
    Just t -> t
    Nothing -> var f



----------------------------------------------------------------
-- Subst instances for List and Fin
----------------------------------------------------------------

-- Scoped List

instance Subst v t => Subst v (List t) where
  applyE r Nil = Nil
  applyE r (x :< xs) = applyE r x :< applyE r xs

-- Fin

instance Shiftable Fin where
  shift = Fin.shiftN

instance SubstVar Fin where
  var x = x

instance {-# OVERLAPS #-} Subst Fin Fin where
  applyE = applyEnv

instance {-# OVERLAPPABLE #-} (SubstVar v) => Subst v Fin where
  applyE = error "BUG: missing isVar definition?"

instance GSubst b Fin where
  gsubst s f = error "BUG: missing isVar definition?"