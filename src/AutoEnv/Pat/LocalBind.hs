-- single binder, but includes a cached name
module AutoEnv.Pat.LocalBind where

import AutoEnv.Classes
import AutoEnv.Pat
import AutoEnv.Lib
import AutoEnv.Env

type LocalName = String

data Box n where
  Box :: LocalName -> Box n
instance Sized Box where
  type Size Box = N1
instance PatEq Box Box where
  patEq (Box _) (Box _) = Just Refl
instance Eq (Box n) where
  x == y = True
instance SubstVar v => (Subst v Box) where
  applyE env (Box x) = Box x
instance FV Box where
  appearsFree _ _ = False
instance Strengthen Box where
  strengthen' m n (Box x) = Just (Box x)
---------------------------------------------------------------
-- LocalBind operations (convenience wrappers for PatBind ops)

type LocalBind v c n = PatBind v c Box n

bind :: Subst v c => c (S n) -> LocalBind v c n
bind = patBind (Box "_internal") 

getLocalName :: LocalBind v c n -> LocalName
getLocalName b = case getPat b of (Box x) -> x

localBind :: Subst v c => LocalName -> c (S n) -> LocalBind v c n
localBind x = patBind (Box x)

unbind :: (Subst v v, Subst v c) => LocalBind v c n -> c (S n)
unbind = getBody

-- unbind, but also provide access to the local name
-- if one is available
lunbind :: (Subst v v, Subst v c) => LocalBind v c n 
  -> ((LocalName , c (S n)) -> d) -> d
lunbind b f = f (getLocalName b, unbind b)

instantiate :: (Subst v c) => LocalBind v c n -> v n -> c n
instantiate b e = instantiatePat b (oneE e)

applyUnder ::
  (Subst v v, Subst v c) =>
  (forall m n. Env v m n -> c m -> c n) ->
  Env v n1 n2 ->
  LocalBind v c n1 ->
  LocalBind v c n2
applyUnder = applyPatUnder