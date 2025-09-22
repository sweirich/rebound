-- |
-- Module       : Rebound.Bind.PatN
-- Description  : Bind a number of variables, without metadata
--
-- Bind a number of variables, with no other information stored with the binder.
-- This is a specialization of "Rebound.Bind.Pat".
module Rebound.Bind.PatN
  ( module Rebound,

    -- * single binder --
    Bind1 (..),
    bind1,
    unbind1,
    unbindl1,
    getBody1,
    instantiate1,
    bindWith1,
    unbindWith1,
    instantiateWith1,
    applyUnder1,

    -- * double binder --
    Bind2 (..),
    bind2,
    unbind2,
    getBody2,
    instantiate2,
    bindWith2,
    unbindWith2,
    instantiateWith2,
    applyUnder2,

    -- * N-ary binder ---
    BindN (..),
    bindN,
    unbindN,
    unbindlN,
    getBodyN,
    instantiateN,
    bindWithN,
    unbindWithN,
    instantiateWithN,
    applyUnderN,
  )
where

import Rebound.Bind.Pat qualified as Pat
import Rebound

import Data.Fin qualified as Fin
import Data.Vec qualified as Vec



----------------------------------------------------------------
-- N-ary patterns
----------------------------------------------------------------

-- * A pattern that binds `p` variables

newtype PatN (p :: Nat) where
  PatN :: SNat p -> PatN p

deriving instance (Eq (PatN p))
deriving instance (TestEquality PatN)

instance SNatI p => SizeIndex PatN p

instance (SNatI p) => Sized (PatN p) where
  type Size (PatN p) = p
  size (PatN sn) = sn

-- | Type binding a number of variables.
-- This data structure includes a delayed
-- substitution for the variables in the body of the binder.
type BindN v c m n = Pat.Bind v c (PatN m) n

-- | Bind a number of variables, using the identity substitution.
bindN :: forall m v c n. (Subst v c, SNatI m) => c (m + n) -> BindN v c m n
bindN = Pat.bind (PatN (snat @m))

-- | Bind a number of variables, while suspending the provided substitution.
bindWithN :: forall p v c m n. (SNatI p) => Env v m n -> c (p + m) -> BindN v c p n
bindWithN = Pat.bindWith (PatN (snat @p))

-- | Run a function on the body, after applying the delayed substitution.
unbindN :: forall m v c n d. (Subst v c, SNatI n, SNatI m) => BindN v c m n -> ((SNatI (m + n)) => c (m + n) -> d) -> d
unbindN bnd f = Pat.unbind bnd (const f)

-- | Retrieve the body of the binding.
-- For this kind of binding, it is equivalent to 'getBody'.
unbindlN :: forall m v c n. (Subst v c, SNatI m) => BindN v c m n -> c (m + n)
unbindlN = Pat.getBody

-- | Retrieve the body of the binding.
getBodyN :: forall m v c n. (Subst v c, SNatI m) => BindN v c m n -> c (m + n)
getBodyN = Pat.getBody

-- | Instantiate the body (i.e. replace the bound variables) with the provided terms.
instantiateN :: (Subst v c, SNatI m) => BindN v c m n -> Vec m (v n) -> c n
instantiateN b v = Pat.instantiate b (fromVec v)

-- | Run a function on the body.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
unbindWithN ::
  (SubstVar v, SNatI m) =>
  BindN v c m n ->
  (forall m1. Env v m1 n -> c (m + m1) -> d) ->
  d
unbindWithN b f = Pat.unbindWith b (const f)

-- | Instantiate the body (i.e. replace the bound variable) with the provided terms.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
instantiateWithN ::
  forall m v c d n.
  (SubstVar v, SNatI n, SNatI m) =>
  BindN v c m n ->
  Vec m (v n) ->
  (forall m. Env v m n -> c m -> d n) ->
  d n
instantiateWithN b v f =
  unbindWithN b (f . appendE (snat @m) (fromVec v))

-- | Apply a function under the binder.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
applyUnderN ::
  (Subst v c2, SNatI k) =>
  (forall m. Env v m (k + n2) -> c1 m -> c2 (k + n2)) ->
  Env v n1 n2 ->
  BindN v c1 k n1 ->
  BindN v c2 k n2
applyUnderN = Pat.applyUnder

----------------------------------------------------------------
-- Single binder
----------------------------------------------------------------

-- | Type binding 1 variable.
-- This data structure includes a delayed
-- substitution for the variables in the body of the binder.
type Bind1 v c n = Pat.Bind v c (PatN N1) n

-- | Bind 1 variable, using the identity substitution.
bind1 :: (Subst v c) => c (S n) -> Bind1 v c n
bind1 = Pat.bind (PatN s1)

-- | Bind 1 variable, while suspending the provided substitution.
bindWith1 :: forall v c m n. Env v m n -> c (S m) -> Bind1 v c n
bindWith1 = Pat.bindWith (PatN s1)

-- | Run a function on the body, after applying the delayed substitution.
unbind1 ::
  forall v c n d.
  (SNatI n, Subst v c) =>
  Bind1 v c n ->
  ((SNatI (S n)) => c (S n) -> d) ->
  d
unbind1 b f = f (Pat.getBody b)

-- | Retrieve the body of the binding.
-- For this kind of binding, it is equivalent to 'getBody'.
unbindl1 :: forall v c n. (Subst v c) => Bind1 v c n -> c (S n)
unbindl1 = Pat.getBody

-- | Retrieve the body of the binding.
getBody1 ::
  forall v c n.
  (Subst v c) =>
  Bind1 v c n ->
  c (S n)
getBody1 = Pat.getBody

-- | Instantiate the body (i.e. replace the bound variable) with the provided term.
instantiate1 :: (Subst v c) => Bind1 v c n -> v n -> c n
instantiate1 b v1 = Pat.instantiate b (v1 .: zeroE)

-- | Run a function on the body.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
unbindWith1 ::
  (SubstVar v) =>
  Bind1 v c n ->
  (forall m. Env v m n -> c (S m) -> d) ->
  d
unbindWith1 b f = Pat.unbindWith b (const f)

-- | Instantiate the body (i.e. replace the bound variable) with the provided terms.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
instantiateWith1 ::
  (SubstVar v) =>
  Bind1 v c n ->
  v n ->
  (forall m. Env v m n -> c m -> d n) ->
  d n
instantiateWith1 b v1 f =
  unbindWith1 b (\r e -> f (v1 .: r) e)

-- | Apply a function under the binder.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
applyUnder1 ::
  (Subst v c2) =>
  (forall m. Env v m (S n2) -> c1 m -> c2 (S n2)) ->
  Env v n1 n2 ->
  Bind1 v c1 n1 ->
  Bind1 v c2 n2
applyUnder1 = Pat.applyUnder

----------------------------------------------------------------
-- Double binder
----------------------------------------------------------------

-- | Type binding 2 variables.
-- This data structure includes a delayed
-- substitution for the variables in the body of the binder.
type Bind2 v c n = Pat.Bind v c (PatN N2) n

-- | Bind 2 variables, using the identity substitution.
bind2 :: (Subst v c) => c (S (S n)) -> Bind2 v c n
bind2 = Pat.bind (PatN s2)

-- | Bind 2 variables, while suspending the provided substitution.
bindWith2 :: forall v c m n. Env v m n -> c (S (S m)) -> Bind2 v c n
bindWith2 = Pat.bindWith (PatN s2)

-- | Run a function on the body, after applying the delayed substitution.
unbind2 ::
  forall v c n d.
  (Subst v c) =>
  Bind2 v c n ->
  (c (S (S n)) -> d) ->
  d
unbind2 b f = f (getBody2 b)

-- | Retrieve the body of the binding.
-- For this kind of binding, it is equivalent to 'getBody'.
unbindl2 :: forall v c n. (Subst v c) => Bind2 v c n -> c (S (S n))
unbindl2 = Pat.getBody

-- | Retrieve the body of the binding.
getBody2 ::
  forall v c n.
  (Subst v c) =>
  Bind2 v c n ->
  c (S (S n))
getBody2 = Pat.getBody

-- | Instantiate the body (i.e. replace the bound variable) with the provided term.
instantiate2 :: (Subst v c) => Bind2 v c n -> v n -> v n -> c n
instantiate2 b v1 v2 = Pat.instantiate b (v1 .: (v2 .: zeroE))

-- | Run a function on the body.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
unbindWith2 ::
  (SubstVar v) =>
  Bind2 v c n ->
  (forall m. Env v m n -> c (S (S m)) -> d) ->
  d
unbindWith2 b f = Pat.unbindWith b (const f)

-- | Instantiate the body (i.e. replace the bound variable) with the provided terms.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
instantiateWith2 ::
  (SubstVar v, SNatI n) =>
  Bind2 v c n ->
  v n ->
  v n ->
  (forall m. Env v m n -> c m -> d n) ->
  d n
instantiateWith2 b v1 v2 f =
  unbindWith2 b (\r e -> f (v1 .: (v2 .: r)) e)

-- | Apply a function under the binder.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
applyUnder2 ::
  (Subst v c2) =>
  (forall m. Env v m (S (S n2)) -> c1 m -> c2 (S (S n2))) ->
  Env v n1 n2 ->
  Bind2 v c1 n1 ->
  Bind2 v c2 n2
applyUnder2 = Pat.applyUnder