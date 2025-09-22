-- |
-- Module       : Rebound.Bind.Single
-- Description  : Bind a single variable, without metadata
--
-- Simplest form of binding: a single variable with no other information stored with the binder.
-- This is a specialization of "Rebound.Bind.PatN".
module Rebound.Bind.Single
  ( module Rebound,
    Bind (..),
    bind,
    unbind,
    unbindl,
    getBody,
    instantiate,
    bindWith,
    unbindWith,
    instantiateWith,
    applyUnder,
  )
where

import Rebound
import Rebound.Bind.PatN
import Rebound.Classes

-- | Type binding a single variable.
-- This data structure includes a delayed
-- substitution for the variables in the body of the binder.
type Bind v c n = Bind1 v c n

-- | Bind a variable, using the identity substitution.
bind :: (Subst v c) => c (S n) -> Bind v c n
bind = bind1

-- | Bind a variable, while suspending the provided substitution.
bindWith :: forall v c m n. Env v m n -> c (S m) -> Bind v c n
bindWith = bindWith1

-- | Run a function on the body, after applying the delayed substitution.
unbind :: forall v c n d. (SNatI n, Subst v c) => Bind v c n -> ((SNatI (S n)) => c (S n) -> d) -> d
unbind = unbind1

-- | Retrieve the body of the binding.
-- For this kind of binding, it is equivalent to 'getBody'.
unbindl :: (Subst v c) => Bind v c n -> c (S n)
unbindl = unbindl1

-- | Retrieve the body of the binding.
getBody :: forall v c n. (Subst v c) => Bind v c n -> c (S n)
getBody = getBody1

-- | Instantiate the body (i.e. replace the bound variable) with the provided term.
instantiate :: (Subst v c) => Bind v c n -> v n -> c n
instantiate = instantiate1

-- | Run a function on the body.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
unbindWith :: (SubstVar v) => Bind v c n -> (forall m. Env v m n -> c (S m) -> d) -> d
unbindWith = unbindWith1

-- | Instantiate the body (i.e. replace the bound variable) with the provided term.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
instantiateWith :: (SubstVar v) => Bind v c n -> v n -> (forall m. Env v m n -> c m -> d n) -> d n
instantiateWith = instantiateWith1

-- | Apply a function under the binder.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
applyUnder :: (Subst v c2) => (forall m. Env v m (S n2) -> c1 m -> c2 (S n2)) -> Env v n1 n2 -> Bind v c1 n1 -> Bind v c2 n2
applyUnder = applyUnder1

