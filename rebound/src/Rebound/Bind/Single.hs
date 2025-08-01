-- | Simplest form of binding: a single variable
-- with no other information stored with the binder
-- (This is a specialization of n-ary binding.)
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

type Bind v c n = Bind1 v c n

bind :: (Subst v c, SNatI n) => c (S n) -> Bind v c n
bind = bind1

bindWith :: forall v c m n. (SNatI m, SNatI n) => Env v m n -> c (S m) -> Bind v c n
bindWith = bindWith1

unbind :: forall v c n d. (SNatI n, Subst v c) => Bind v c n -> ((SNatI (S n)) => c (S n) -> d) -> d
unbind = unbind1

unbindl :: (Subst v c, SNatI n) => Bind v c n -> c (S n)
unbindl = unbindl1

getBody :: forall v c n. (Subst v c, SNatI n) => Bind v c n -> c (S n)
getBody = getBody1

instantiate :: (Subst v c, SNatI n) => Bind v c n -> v n -> c n
instantiate = instantiate1

unbindWith :: (SubstVar v) => Bind v c n -> (forall m. Env v m n -> c (S m) -> d) -> d
unbindWith = unbindWith1

instantiateWith :: (SubstVar v, SNatI n) => Bind v c n -> v n -> (forall m n. SNatI n => Env v m n -> c m -> d n) -> d n
instantiateWith = instantiateWith1

applyUnder :: (Subst v c2, SNatI n2) => (forall m n. Env v m n -> c1 m -> c2 n) -> Env v n1 n2 -> Bind v c1 n1 -> Bind v c2 n2
applyUnder = applyUnder1

