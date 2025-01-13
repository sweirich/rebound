-- | A "Simple" pattern can bind variables but 
-- cannot contain references to free variables in scope 
-- (i.e. in a type annotation).

-- The pattern type must have kind `Type`

module AutoEnv.Pat.Simple where

import AutoEnv.Lib
import AutoEnv.Classes
import AutoEnv.Env

-- A pattern is any type that can be made an instance of the
-- `Sized` type class below

----------------------------------------------------------
-- Sized type class for patterns
----------------------------------------------------------

-- | Calculate the number of binding variables in the pattern
-- This number does not need to be an explicit parameter of the type
-- so that we have flexibility about what types we can use as 
-- patterns. 
class Sized (t :: Type) where
  -- Retrieve size from the type
  type Size t :: Nat
  -- Access size as a term
  size :: t -> SNat (Size t)
  -- size _ = snat

-- | Pairs of types that can be compared with each other as patterns
class PatEq (t1 :: Type) (t2 :: Type) where
    patEq :: t1 -> t2 -> Maybe (Size t1 :~: Size t2)

----------------------------------------------------------
-- Pattern binding (N-ary binding)
----------------------------------------------------------

-- The `Bind` type binds `Size pat` variables.
-- This data structure includes a delayed
-- substitution for the variables in the body of the binder.
data Bind v c (pat :: Type) (n :: Nat) where
  Bind ::
    pat ->
    Env v m n ->
    c (Plus (Size pat) m) ->
    Bind v c pat n

-- | Create a `Bind` with an identity substitution.
bind ::
  forall v c pat n.
  (Sized pat, Subst v c) =>
  pat ->
  c (Plus (Size pat) n) ->
  Bind v c pat n
bind pat = Bind pat idE

-- | Access the pattern of a pattern binding
getPat :: Bind v c pat n -> pat
getPat (Bind pat env t) = pat

-- | Access the body of a pattern binding.
-- The pattern type determines the number of variables
-- bound in the pattern
getBody ::
  forall v c pat n.
  (Sized pat, Subst v v, Subst v c) =>
  Bind v c pat n ->
  c (Plus (Size pat) n)
getBody (Bind (pat :: pat) (env :: Env v m n) t) =
  applyE @v @c @(Plus (Size pat) m) (upN (size pat) env) t

-- | instantiate the body with terms for each variable in the pattern
instantiate ::
  forall v c pat n.
  (Sized pat, Subst v c) =>
  Bind v c pat n ->
  Env v (Size pat) n ->
  c n
instantiate b e =
  unBindWith
    b
    (\p r t -> withSNat (size p) $ applyE (e .++ r) t)

-- | apply an environment-parameterized function while instantiating  
instantiateWith ::
  (Sized pat, SubstVar v) =>
  Bind v c pat n ->
  Env v (Size pat) n ->
  (forall m n. Env v m n -> c m -> c n) ->
  c n
instantiateWith b v f = unBindWith b (\p r e -> withSNat (size p) $ f (v .++ r) e)
  

  
-- | unbind a binder and apply the function to the pattern and subterm  
-- in a context where the extended size is available at runtime.
unbind ::
  forall v c pat n d.
  (SNatI n, Sized pat, Subst v v, Subst v c) =>
  Bind v c pat n ->
  (forall m. (SNatI m, m ~ Plus (Size pat) n) => pat -> c m -> d) ->
  d
unbind bnd f =
  withSNat (sPlus (size (getPat bnd)) (snat @n)) $
    f (getPat bnd) (getBody bnd)

-- | Apply a function to the pattern, suspended environment, and body
-- in a pattern binding
unBindWith ::
  (Sized pat, SubstVar v) =>
  Bind v c pat n ->
  (forall m. pat -> Env v m n -> c (Plus (Size pat) m )-> d) ->
  d
unBindWith (Bind pat (r :: Env v m n) t) f = 
  f pat r t

-- | apply an environment-parameterized function & environment
-- underneath a binder
applyUnder ::
  (Sized pat, Subst v v, Subst v c) =>
  (forall m n. Env v m n -> c m -> c n) ->
  Env v n1 n2 ->
  Bind v c pat n1 ->
  Bind v c pat n2
applyUnder f r2 (Bind p r1 t) =
  Bind p idE (f r' t)
  where
    r' = upN (size p) (r1 .>> r2)
    

-----------------------------------------------------------------
-- instances for Bind (Subst, FV, Strengthen)
-----------------------------------------------------------------

-- | The substitution operation composes the explicit
-- substitution with the one stored at the binder
instance (Subst v v) => Subst v (Bind v c p) where
  applyE env1 (Bind p env2 m) = Bind p (env2 .>> env1) m

instance
  ( Subst v v,
    Subst v c,
    Sized p,
    FV c
  ) =>
  FV (Bind v c p)
  where
  appearsFree n b =
    let pat = getPat b
     in appearsFree (shiftN (size pat) n) (getBody b)

instance
  (Sized p, SubstVar v, Subst v v, Subst v c, Strengthen c) =>
  Strengthen (Bind v c p)
  where
  strengthen' (m :: SNat m) (n :: SNat n) (Bind p (env :: Env v m' n') t) =
    case axiomM @m @(Size p) @n of
      Refl -> 
        withSNat n $ 
           bind p <$> strengthen' m (sPlus (size p) n) 
              (applyE @v @c @(Plus (Size p) m') (upN (size p) env) t)
          
-----------------------------------------------------------------
-- Rebind 
---------------------------------------------------------------

data Rebind p1 p2 n where
  Rebind :: p1 -> p2 (Plus (Size p1) n) -> Rebind p1 p2 n

instance
  (Subst v v, Sized p1, Subst v p2) =>
  Subst v (Rebind p1 p2)
  where
  applyE ::
    (Subst v v, Sized p1, Subst v p2) =>
    Env v n m ->
    Rebind p1 p2 n ->
    Rebind p1 p2 m
  applyE r (Rebind p1 p2) = Rebind p1 (applyE (upN (size p1) r) p2)


instance (Sized p1, FV p2) => FV (Rebind p1 p2) where
  appearsFree :: (Sized p1, FV p2) => Fin n -> Rebind p1 p2 n -> Bool
  appearsFree n (Rebind p1 p2) = appearsFree (shiftN (size p1) n) p2


instance (Sized p1, Strengthen p2) => Strengthen (Rebind p1 p2) where
  strengthen' ::
    forall m n p.
    SNat m ->
    SNat n ->
    Rebind p1 p2 (Plus m n) ->
    Maybe (Rebind p1 p2 n)
  strengthen' m n (Rebind p1 p2) =
    case axiomM @m @(Size p1) @n of
      Refl ->
        Rebind p1
          <$> strengthen' m (sPlus (size p1) n) p2

  