-- single binder, but includes a cached name
module AutoEnv.Pat.LocalBind where

import AutoEnv.Classes
import qualified AutoEnv.Pat.Simple as Pat
import AutoEnv.Lib
import AutoEnv.Env


newtype LocalName = Box { name :: String}
  deriving (Eq)

instance Show LocalName where
  show (Box x) = x
  
internalName :: LocalName
internalName = Box "_internal"

instance Pat.Sized LocalName where
  type Size LocalName = N1
  size _ = s1

{-
instance Pat.PatEq LocalName LocalName where
  patEq (Box _) (Box _) = Just Refl

instance Eq LocalName where
  x == y = True
-}
---------------------------------------------------------------
-- LocalBind operations (convenience wrappers)

type Bind v c n = Pat.Bind v c LocalName n

bind :: (SNatI n, Subst v c) => LocalName -> c (S n) -> Bind v c n
bind = Pat.bind

getLocalName :: Bind v c n -> LocalName
getLocalName = Pat.getPat

internalBind :: (SNatI n, Subst v c) => c (S n) -> Bind v c n
internalBind = Pat.bind internalName

getBody :: (Subst v v, Subst v c) => Bind v c n -> c (S n)
getBody = Pat.getBody

-- unbind, but also provide access to the local name
-- if one is available
unbind :: (Subst v v, Subst v c) => Bind v c n 
  -> ((LocalName , c (S n)) -> d) -> d
unbind b f = f (getLocalName b, getBody b)

instantiate :: (Subst v c) => Bind v c n -> v n -> c n
instantiate b e = Pat.instantiate b (oneE e)

applyUnder ::
  (SNatI n2, Subst v v, Subst v c) =>
  (forall m n. Env v m n -> c m -> c n) ->
  Env v n1 n2 ->
  Bind v c n1 ->
  Bind v c n2
applyUnder = Pat.applyUnder

-- TODO: unbindWith
-- TODO: instantiatiateWith