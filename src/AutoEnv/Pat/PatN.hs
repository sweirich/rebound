module AutoEnv.Pat.PatN where

import AutoEnv.Lib
import AutoEnv.Classes
import AutoEnv.Pat
import AutoEnv.Env

----------------------------------------------------------------
-- N-ary patterns
----------------------------------------------------------------

-- * A pattern that binds `p` variables
data PatN (p :: Nat) (n :: Nat) where
  PatN :: SNat p -> PatN p n

instance Sized (PatN p) where
  type Size (PatN p) = p
  size (PatN sn) = sn

instance (SubstVar v) => Subst v (PatN p) where
  applyE r (PatN sn) = PatN sn

instance Strengthen (PatN p) where
  strengthen' m n (PatN sn) = Just (PatN sn)

instance FV (PatN p) where
    appearsFree _ _ = False

instance Alpha (PatN p) where
    aeq _ _ = True

instance PatEq (PatN p1) (PatN p2) where
    patEq (PatN sn1) (PatN sn2) = testEquality sn1 sn2

----------------------------------------------------------------
-- Double binder
----------------------------------------------------------------

-- A double binder is just a pattern binding with
-- "SNat 2" as the pattern

type Bind2 v c n = PatBind v c (PatN N2) n

bind2 :: (Subst v c) => c (S (S n)) -> Bind2 v c n
bind2 = patBind (PatN s2)

unbind2 :: forall v c n. (Subst v v, Subst v c) => Bind2 v c n -> c (S (S n))
unbind2 = getBody

unbind2With ::
  (SubstVar v) =>
  Bind2 v c n ->
  (forall m. Env v m n -> c (S (S m)) -> d) ->
  d
unbind2With b f = unPatBindWithEnv b (const f)

instantiate2 :: (Subst v c) => Bind2 v c n -> v n -> v n -> c n
instantiate2 b v1 v2 = instantiatePat b (v1 .: (v2 .: zeroE))

instantiate2With ::
  (SubstVar v) =>
  Bind2 v c n ->
  v n ->
  v n ->
  (forall m n. Env v m n -> c m -> c n) ->
  c n
instantiate2With b v1 v2 f =
  unbind2With b (\r e -> f (v1 .: (v2 .: r)) e)