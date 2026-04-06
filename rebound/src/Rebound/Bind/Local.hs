-- |
-- Module       : Rebound.Bind.Local
-- Description  : Bind a single variable, with a name
--
-- Binders that includes a name (represented by a 'LocalName') for pretty printing.
-- This is a specialization of "Rebound.Bind.Pat".
module Rebound.Bind.Local
  ( module Rebound,
    module Data.Vec,
    module Data.LocalName,

    -- * Single binder --
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
    instantiateWith,

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

    -- * Double binder --
    Bind2 (..),
    bind2,
    unbind2,
    getBody2,
    getLocalName2,
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
    getLocalNameN,
    instantiateN,
    bindWithN,
    unbindWithN,
    instantiateWithN,
    applyUnderN,
  )
where

import Data.Fin qualified as Fin
import Data.Vec qualified as Vec
import Data.Vec (Vec(..))
import Data.LocalName
import Rebound
import Rebound.Bind.Pat qualified as Pat
import Rebound.Env qualified as Env



-- * -- Single Binder

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


-- | Type binding a single variable.
-- This data structure includes a delayed
-- substitution for the variables in the body of the binder.
type Bind1 v c n = Bind v c n

-- | Bind a variable, using the identity substitution.
bind1 :: (Subst v c) => LocalName -> c (S n) -> Bind1 v c n
bind1 = bind

-- | Bind a variable, while suspending the provided substitution.
bindWith1 :: forall v c m n. LocalName -> Env v m n -> c (S m) -> Bind1 v c n
bindWith1 = bindWith

-- | Bind the default \"internal\" variable, while suspending the provided substitution.
internalBind1 :: (Subst v c) => c (S n) -> Bind1 v c n
internalBind1 = internalBind

-- | Retrieve the name of the bound variable.
getLocalName1 :: Bind1 v c n -> LocalName
getLocalName1 = getLocalName

-- | Retrieve the body of the binding.
getBody1 :: (Subst v c) => Bind1 v c n -> c (S n)
getBody1 = getBody

-- | Run a function on the body (and bound name), after applying the delayed substitution.
unbind1 :: (Subst v c) => Bind1 v c n -> ((LocalName, c (S n)) -> d) -> d
unbind1 = unbind

-- | Retrieve the body, as well as the bound name.
unbindl1 :: (Subst v c) => Bind1 v c n -> (LocalName, c (S n))
unbindl1 = unbindl

-- | Instantiate the body (i.e. replace the bound variable) with the provided term.
instantiate1 :: (Subst v c) => Bind1 v c n -> v n -> c n
instantiate1 = instantiate 

-- | Apply a function under the binder.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
applyUnder1 ::
  (Subst v c) =>
  (forall m. Env v m (S n2) -> c m -> c (S n2)) ->
  Env v n1 n2 ->
  Bind1 v c n1 ->
  Bind1 v c n2
applyUnder1 = applyUnder

-- | Run a function on the body.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
unbindWith1 :: (SubstVar v) => Bind1 v c n -> (forall m. LocalName -> Env v m n -> c (S m) -> d) -> d
unbindWith1 = unbindWith

-- | Instantiate the body (i.e. replace the bound variable) with the provided term.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
instantiateWith1 :: (SubstVar v) => Bind1 v c n -> v n -> (forall m. Env v m n -> c m -> c n) -> c n
instantiateWith1 = instantiateWith



-- * -- Double Binder

-- | Type binding a single variable.
-- This data structure includes a delayed
-- substitution for the variables in the body of the binder.
type Bind2 v c n = Pat.Bind v c (Vec N2 LocalName) n

-- | Bind a variable, using the identity substitution.
bind2 :: (Subst v c) => LocalName -> LocalName -> c (S (S n)) -> Bind2 v c n
bind2 x y = Pat.bind (x ::: (y ::: VNil))

-- | Bind a variable, while suspending the provided substitution.
bindWith2 :: forall v c m n. LocalName -> LocalName -> Env v m n -> c (S (S m)) -> Bind2 v c n
bindWith2 x y = Pat.bindWith (x ::: (y ::: VNil))

-- | Bind the default \"internal\" variable, while suspending the provided substitution.
internalBind2 :: (Subst v c) => c (S (S n)) -> Bind2 v c n
internalBind2 = Pat.bind (internalName ::: internalName ::: VNil)

-- | Retrieve the names of the bound variable.
getLocalName2 :: Bind2 v c n -> Vec N2 LocalName
getLocalName2 = Pat.getPat

-- | Retrieve the body of the binding.
getBody2 :: (Subst v c) => Bind2 v c n -> c (S (S n))
getBody2 = Pat.getBody

-- | Run a function on the body (and bound name), after applying the delayed substitution.
unbind2 :: (Subst v c) => Bind2 v c n -> ((Vec N2 LocalName, c (S (S n))) -> d) -> d
unbind2 b f = f (getLocalName2 b, getBody2 b)

-- | Retrieve the body, as well as the bound name.
unbindl2 :: (Subst v c) => Bind2 v c n -> (Vec N2 LocalName, c (S (S n)))
unbindl2 b = (getLocalName2 b, getBody2 b)

-- | Instantiate the body (i.e. replace the bound variable) with the provided term.
instantiate2 :: (Subst v c) => Bind2 v c n -> v n -> v n -> c n
instantiate2 b e1 e2 = Pat.instantiate b (e1 .: (e2 .: zeroE))

-- | Apply a function under the binder.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
applyUnder2 ::
  (Subst v c) =>
  (forall m. Env v m (S (S n2)) -> c m -> c (S (S n2))) ->
  Env v n1 n2 ->
  Bind2 v c n1 ->
  Bind2 v c n2
applyUnder2 = Pat.applyUnder

-- | Run a function on the body.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
unbindWith2 :: (SubstVar v) => Bind2 v c n -> 
   (forall m. LocalName -> LocalName -> Env v m n -> c (S (S m)) -> d) -> d
unbindWith2 b f = Pat.unbindWith b (\ v e b2 -> f (v Vec.! FZ) (v Vec.! (FS FZ)) e b2)

-- | Instantiate the body (i.e. replace the bound variable) with the provided term.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
instantiateWith2 :: (SubstVar v) => 
  Bind2 v c n -> v n -> v n -> (forall m. Env v m n -> c m -> c n) -> c n
instantiateWith2 b v1 v2 = Pat.instantiateWith b (v1 .: (v2 .: zeroE))


type BindN v c m n = Pat.Bind v c (Vec m LocalName) n


-- | Bind a number of variables, using the identity substitution.
bindN :: forall m v c n. (Subst v c, SNatI m) => Vec m LocalName -> c (m + n) -> BindN v c m n
bindN = Pat.bind 

-- | Bind a number of variables, while suspending the provided substitution.
bindWithN :: forall p v c m n. (SNatI p) => Vec p LocalName -> Env v m n -> c (p + m) -> BindN v c p n
bindWithN = Pat.bindWith 

-- | Run a function on the body, after applying the delayed substitution.
unbindN :: forall m v c n d. (Subst v c, SNatI n, SNatI m) => 
   BindN v c m n -> ((SNatI (m + n)) => Vec m LocalName -> c (m + n) -> d) -> d
unbindN bnd f = Pat.unbind bnd f

-- | Retrieve the body of the binding.
-- For this kind of binding, it is equivalent to 'getBodyN'.
unbindlN :: forall m v c n. (Subst v c, SNatI m) => BindN v c m n -> c (m + n)
unbindlN = Pat.getBody

-- | Retrieve the body of the binding.
getBodyN :: forall m v c n. (Subst v c, SNatI m) => BindN v c m n -> c (m + n)
getBodyN = Pat.getBody

getLocalNameN :: BindN v c m n -> Vec m LocalName
getLocalNameN = Pat.getPat

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
