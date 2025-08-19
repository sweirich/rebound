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

bind :: (Subst v c) => LocalName -> c (S n) -> Bind v c n
bind = Pat.bind

bindWith :: forall v c m n. LocalName -> Env v m n -> c (S m) -> Bind v c n
bindWith = Pat.bindWith 

getLocalName :: Bind v c n -> LocalName
getLocalName = Pat.getPat

internalBind :: (Subst v c) => c (S n) -> Bind v c n
internalBind = Pat.bind internalName

getBody :: (Subst v c) => Bind v c n -> c (S n)
getBody = Pat.getBody

-- unbind, but also provide access to the local name
unbind :: (Subst v c) => Bind v c n -> ((LocalName, c (S n)) -> d) -> d
unbind b f = f (getLocalName b, getBody b)

unbindl :: (Subst v c) => Bind v c n -> (LocalName, c (S n))
unbindl b = (getLocalName b, getBody b)

instantiate :: (Subst v c) => Bind v c n -> v n -> c n
instantiate b e = Pat.instantiate b (oneE e)

applyUnder ::
  (Subst v c) =>
  (forall m. Env v m (S n2) -> c m -> c (S n2)) ->
  Env v n1 n2 ->
  Bind v c n1 ->
  Bind v c n2
applyUnder = Pat.applyUnder

unbindWith :: (SubstVar v) => Bind v c n -> (forall m. LocalName -> Env v m n -> c (S m) -> d) -> d
unbindWith = Pat.unbindWith

instantiateWith :: (SubstVar v) => Bind v c n -> v n -> (forall m. Env v m n -> c m -> c n) -> c n
instantiateWith b v = Pat.instantiateWith b (oneE v)


-- Example

data Exp n = Var (Fin n) | App (Exp n) (Exp n) | Lam (Bind Exp Exp n) 
  deriving (Eq,Generic1)
instance SubstVar Exp where var = Var
instance Subst Exp Exp where 
  isVar (Var x) = Just (Refl,x)
  isVar _ = Nothing
t1 :: Exp Z
t1 = Lam (bind (LocalName "x") (Var Fin.f0))
t2 :: Exp Z
t2 = Lam (bind (LocalName "y") (Var Fin.f0))

-- >>> t1 == t2
-- True
