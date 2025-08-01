{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}

-- |
-- Module      : Rebound.Env
-- Description : Environments
-- Stability   : experimental
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
    withScope
  )
where

import Rebound.Classes (Shiftable (..))
import Rebound.Env.Vector
import Rebound.Lib
import Control.Monad
import Data.Scoped.List (List, pattern Nil, pattern (:<))

import Data.Fin qualified as Fin
import Data.Map qualified as Map
import Data.Vec qualified as Vec
import Data.SNat qualified as SNat
import GHC.Generics hiding (S)
import Prelude hiding (head, tail)

----------------------------------------------
-- operations on environments/substitutions
----------------------------------------------

-- TODO: do we want to replace uses of this operation with something else?
env :: forall m v n. (SubstVar v, SNatI m, SNatI n) => (Fin m -> v n) -> Env v m n
env f = fromVec v
  where
    v :: Vec m (v n)
    v = Vec.tabulate f

-- | A singleton environment (single index domain)
-- maps that single variable to `v n`
oneE :: (SubstVar v, SNatI n) => v n -> Env v (S Z) n
oneE v = v .: zeroE

-- | an environment that maps index 0 to v and leaves
-- all other indices alone.
singletonE :: (SubstVar v, SNatI n) => v n -> Env v (S n) n
singletonE v = v .: idE

-- | identity environment, any size
idE :: (SubstVar v, SNatI n) => Env v n n
idE = shiftNE s0

-- | append two environments
-- The `SNatI` constraint is a runtime witness for the length
-- of the domain of the first environment. By using a class
-- constraint, this can be an infix operation.
(.++) ::
  (SNatI p, SubstVar v) =>
  Env v p n ->
  Env v m n ->
  Env v (p + m) n
(.++) = appendE snat

-- | append two environments: explicit length `SNat p` required
-- for the domain of the first list
appendE ::
  (SubstVar v) =>
  SNat p ->
  Env v p n ->
  Env v m n ->
  Env v (p + m) n
appendE p = getAppendE (withSNat p (induction base step)) where
  base = MkAppendE $ \e1 e2 -> e2
  step :: SubstVar v => AppendE v m n p -> AppendE v m n (S p)
  step (MkAppendE r) = MkAppendE $ \e1 e2 -> 
    withScope e1 $
       head e1 .: r (tail e1) e2

newtype AppendE v m n p =
     MkAppendE { getAppendE :: 
       Env v p n ->
       Env v m n ->
       Env v (p + m) n }
       
-- | access value at index 0
head :: (SubstVar v) => Env v (S n) m -> v m
head f = applyEnv f f0

-- | increment all free variables by 1
shift1E :: (SubstVar v, SNatI n) => Env v n (S n)
shift1E = shiftNE s1

-- | Shift an environment by size `p`
upN :: forall v p m n.
  (Subst v v, SNatI n) =>
  SNat p ->
  Env v m n ->
  Env v (p + m) (p + n)
upN p = getUpN @_ @_ @_ @p (withSNat p (induction base step)) p where
   base :: UpN v m n Z
   base = MkUpN (const id)
   step :: forall p1. UpN v m n p1 -> UpN v m n (S p1)
   step (MkUpN r) = MkUpN 
    $ \p e -> withSNat (sPlus (SNat.prev p) (snat @n)) $ var Fin.f0 .: (r (SNat.prev p) e .>> shiftNE s1)

newtype UpN v m n p = 
    MkUpN { getUpN :: SNat p -> Env v m n -> Env v (p + m) (p + n) }

shiftFromApplyE :: forall v c k n. (SubstVar v, Subst v c, SNatI n) => SNat k -> c n -> c (k + n)
shiftFromApplyE k = applyE @v (shiftNE k)

----------------------------------------------------
-- Create an environment from a length-indexed
-- vector of scoped values

fromVec :: (SubstVar v, SNatI n) => Vec m (v n) -> Env v m n
fromVec v = getEnv (Vec.induction v base step) where
  base :: SNatI n => EnvN v n Z
  base = EnvN zeroE
  step :: (SubstVar v, SNatI n) => v n -> EnvN v n m -> EnvN v n (S m)
  step x (EnvN r) = EnvN (x .: r)

newtype EnvN v n m = EnvN { getEnv :: Env v m n } 

toVec :: forall v m n. (SubstVar v) => SNat m -> Env v m n -> Vec m (v n)
toVec m = getVec ind
  where
    ind :: VecN v n m
    ind = withSNat m $ SNat.induction @_ @(VecN v n) base indS

    base :: VecN v n Z
    base = VecN (\_ -> Vec.empty)
    indS :: forall m. VecN v n m -> VecN v n (S m)
    indS (VecN t') = VecN (\r -> head r |> t' (tail r))

newtype VecN v n m = VecN { getVec :: Env v m n -> Vec m (v n) }

----------------------------------------------------------------
-- show for environments
----------------------------------------------------------------

instance (SNatI n, Show (v m), SubstVar v) => Show (Env v n m) where
  show x = show (tabulate x)

tabulate :: (SNatI n, Subst v v) => Env v n m -> [(Fin n, v m)]
tabulate r = map (\f -> (f, applyEnv r f)) Fin.universe

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