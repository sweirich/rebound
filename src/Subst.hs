module Subst where

import Vec
import Data.Kind
import Data.List as List

-- This module defines the type `Env v m n` i.e. 
-- an environment mapping indices up to size m, to 
-- values of type `v n`

-- It also defines two classes for working with this
-- type.


----------------------------------------------
-- Class of well-scoped types that support working with 
-- environments (i.e. explicit substitutions)

class SubstVar (v :: Nat -> Type) where
    var    :: Fin n -> v n

-- Apply an environment to a well-scoped term
class SubstVar v => Subst v c where
    applyE :: Env v n m -> c n -> c m

----------------------------------------------
-- environments as functions

newtype Env v m n = Env { applyEnv :: Fin m -> v n }

-- identity environment
idE :: SubstVar v => Env v n n
idE = Env var

-- composition
(.>>) :: Subst v v => Env v p n -> Env v n m -> Env v p m
f .>> g = Env $ applyE g . applyEnv f

-- an environment that maps index 0 to v and leaves 
-- everthing else alone
singleE :: SubstVar v => v n -> Env v n n
singleE v = Env $ \ case FZ -> v ; FS y -> var (FS y)

-- `cons` -- extend an environment with a new mapping 
-- for index '0'. All existing mappings are shifted over.
(.:) :: SubstVar v => v m -> Env v n m -> Env v (S n) m
v .: f = Env $ \ case FZ -> v ; (FS x) -> applyEnv f x 

-- inverse of `cons` -- remove the first mapping
tailE :: SubstVar v => Env v (S n) m -> Env v n m
tailE f = Env (applyEnv f . FS )

headE :: SubstVar v => Env v (S n) m -> v m
headE f = applyEnv f FZ

-- modify an environment so that it can go under 
-- a binder
upE :: Subst v v => Env v m n -> Env v (S m) (S n)
upE e = var FZ .: (e .>> shiftE)

shiftE :: SubstVar v => Env v n (S n)
shiftE = Env (var . FS)


----------------------------------------------------------------
----------------------------------------------------------------
-- Single binders, with an embedded substitution
-- n is the number of free variables in the term
data Bind1 v c (n :: Nat) where
    Bind1 :: Env v m n -> c (S m) -> Bind1 v c n

-- The substitution operation composes the explicit 
-- substitution with the one stored at the binder
instance Subst v v => Subst v (Bind1 v c) where
    -- applyE :: SubstVar v => (Fin n -> v m) -> Bind1 v c n -> Bind1 v c m
    applyE env1 (Bind1 env2 m) = Bind1 (env2 .>> env1) m

-- | create a single binder
bind1 :: Subst v c => c (S n) -> Bind1 v c n
bind1 = Bind1 idE

-- | instantiate a binder with a term
instantiate :: forall v c n. (Subst v c) => Bind1 v c n -> v n -> c n
-- instantiate = instantiateWith applyE
instantiate b v = unbindWith (\ r e -> applyE (v .: r) e) b

-- | access the body of the binder  (inverse of bind)
unbind :: forall v c n. (Subst v v, Subst v c) => Bind1 v c n -> c (S n)
unbind (Bind1 env t) = applyE (upE env) t

-- | unbind a binder and apply the function to the argument and subterm.
unbindWith :: (SubstVar v) => 
    (forall m. Env v m n -> c (S m) -> d) ->
    Bind1 v c n -> d
unbindWith f (Bind1 r t) = f r t

-- | apply an environment-parameterized function & environment 
-- underneath a binder
applyWith :: (Subst v v, Subst v c) =>
        (forall m n. Env v m n -> c m -> c n) -> Env v n1 n2 ->
        Bind1 v c n1 -> Bind1 v c n2
applyWith f r2 (Bind1 r1 t) = bind1 (f (upE r1 .>> upE r2) t)

-- | apply an environment-parameterized function to an instantiated
-- binder
instantiateWith :: (SubstVar v) =>
         (forall m n. Env v m n -> c m -> c n) ->
         Bind1 v c n -> v n -> c n
-- instantiateWith f (Bind1 r e) v = f (v .: r) e
instantiateWith f b v = unbindWith (\ r e -> f ( v .: r) e) b


----------------------------------------------------------------
-- Double binder
-- TODO: fill this out as above

data Bind2 v c (n :: Nat) where
    Bind2 :: Env v m n -> c (S (S m)) -> Bind2 v c n

bind2 :: Subst v c => c (S (S n)) -> Bind2 v c n
bind2 = Bind2 (Env var)

instance Subst v v => Subst v (Bind2 v c) where
    applyE :: SubstVar v => Env v n m -> Bind2 v c n -> Bind2 v c m
    applyE env1 (Bind2 env2 m) = Bind2 (env2 .>> env1) m

-- TODO: n-ary binders


