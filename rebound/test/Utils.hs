module Utils where

import Rebound (Env, SNat (..), SNatI, SubstVar, head, snat, tail, withSNat)
import Prelude hiding (head, tail)

envEq ::
  forall v n m.
  (SNatI n, forall k. Eq (v k), SubstVar v) =>
  Env v n m ->
  Env v n m ->
  Bool
envEq l r = case snat @n of
  SZ -> True
  SS -> head l == head r && envEq (tail l) (tail r)

instance {-# OVERLAPPING #-} (forall k. Eq (v k), SubstVar v) => Eq (SNat n, Env v n m) where
  (n, l) == (_, r) = withSNat n $ envEq l r
