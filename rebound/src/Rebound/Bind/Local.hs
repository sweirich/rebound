-- | single binder, but includes a name for pretty printing
-- type synonym for Pat.Bind with an opaque name as the pattern
module Rebound.Bind.Local
  ( module Rebound,
    type Bind,
    bind,
    getLocalName,
    internalBind,
    getBody,
    unbind,
    unbindl,
    instantiate,
    applyUnder,
    bindWith,
    unbindWith,
    instantiateWith
  )
where

import Rebound
import Rebound.Bind.Pat qualified as Pat
import Data.Fin qualified as Fin

---------------------------------------------------------------
-- LocalBind operations (convenience wrappers)

type Bind v c n = Pat.Bind v c LocalName n

bind :: (Subst v c, SNatI n) => LocalName -> c (S n) -> Bind v c n
bind = Pat.bind

bindWith :: forall v c m n. (SNatI m, SNatI n) => LocalName -> Env v m n -> c (S m) -> Bind v c n
bindWith = Pat.bindWith 

getLocalName :: Bind v c n -> LocalName
getLocalName = Pat.getPat

internalBind :: (SNatI n) => (Subst v c) => c (S n) -> Bind v c n
internalBind = Pat.bind internalName

getBody :: SNatI n => (Subst v c) => Bind v c n -> c (S n)
getBody = Pat.getBody

-- unbind, but also provide access to the local name
unbind :: (Subst v c, SNatI n) => Bind v c n -> ((LocalName, c (S n)) -> d) -> d
unbind b f = f (getLocalName b, getBody b)

unbindl :: (Subst v c, SNatI n) => Bind v c n -> (LocalName, c (S n))
unbindl b = (getLocalName b, getBody b)

instantiate :: (Subst v c, SNatI n) => Bind v c n -> v n -> c n
instantiate b e = Pat.instantiate b (oneE e)

applyUnder ::
  (Subst v c, SNatI n2) =>
  (forall m n. Env v m n -> c m -> c n) ->
  Env v n1 n2 ->
  Bind v c n1 ->
  Bind v c n2
applyUnder = Pat.applyUnder

unbindWith :: (SubstVar v) => Bind v c n -> (forall m. LocalName -> Env v m n -> c (S m) -> d) -> d
unbindWith = Pat.unbindWith

instantiateWith :: (SubstVar v, SNatI n) => Bind v c n -> v n -> (forall m n. Env v m n -> c m -> c n) -> c n
instantiateWith b v = Pat.instantiateWith b (oneE v)

