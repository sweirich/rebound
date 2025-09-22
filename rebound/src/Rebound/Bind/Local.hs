-- |
-- Module       : Rebound.Bind.Single
-- Description  : Bind a single variable, with a name
--
-- Single variable binder, but includes a name (represented by a 'LocalName') for pretty printing.
-- This is a specialization of "Rebound.Bind.Pat".
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

-- | Type binding a single variable.
-- This data structure includes a delayed
-- substitution for the variables in the body of the binder.
type Bind v c n = Pat.Bind v c LocalName n

-- | Bind a variable, using the identity substitution.
bind :: (Subst v c) => LocalName -> c (S n) -> Bind v c n
bind = Pat.bind

-- | Bind a variable, while suspending the provided substitution.
bindWith :: forall v c m n. LocalName -> Env v m n -> c (S m) -> Bind v c n
bindWith = Pat.bindWith

-- | Bind the default \"internal\" variable, while suspending the provided substitution.
internalBind :: (Subst v c) => c (S n) -> Bind v c n
internalBind = Pat.bind internalName

-- | Retrieve the name of the bound variable.
getLocalName :: Bind v c n -> LocalName
getLocalName = Pat.getPat

-- | Retrieve the body of the binding.
getBody :: (Subst v c) => Bind v c n -> c (S n)
getBody = Pat.getBody

-- | Run a function on the body (and bound name), after applying the delayed substitution.
unbind :: (Subst v c) => Bind v c n -> ((LocalName, c (S n)) -> d) -> d
unbind b f = f (getLocalName b, getBody b)

-- | Retrieve the body, as well as the bound name.
unbindl :: (Subst v c) => Bind v c n -> (LocalName, c (S n))
unbindl b = (getLocalName b, getBody b)

-- | Instantiate the body (i.e. replace the bound variable) with the provided term.
instantiate :: (Subst v c) => Bind v c n -> v n -> c n
instantiate b e = Pat.instantiate b (oneE e)

-- | Apply a function under the binder.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
applyUnder ::
  (Subst v c) =>
  (forall m. Env v m (S n2) -> c m -> c (S n2)) ->
  Env v n1 n2 ->
  Bind v c n1 ->
  Bind v c n2
applyUnder = Pat.applyUnder

-- | Run a function on the body.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
unbindWith :: (SubstVar v) => Bind v c n -> (forall m. LocalName -> Env v m n -> c (S m) -> d) -> d
unbindWith = Pat.unbindWith

-- | Instantiate the body (i.e. replace the bound variable) with the provided term.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
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
