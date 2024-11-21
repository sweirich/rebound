{-# LANGUAGE DefaultSignatures #-}
module AutoEnv.Pat where

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
-- so that we have more flexibility about what types we can use as 
-- patterns. However, the scope of the pattern needs to be the last 
-- parameter.
class Sized (t :: Nat -> Type) where
  type Size t :: Nat
  -- recover the size of the pattern as a dynamic term
  -- it is usually not a good idea to use this function, if it 
  -- can be avoided 
  size :: t n -> SNat (Size t)
  -- If `SNatI (Size t)` is available, then the default definition 
  -- of the operation just uses that value
  default size :: SNatI (Size t) => t n -> SNat (Size t)
  size _ = snat @(Size t)

-- | Pairs of types that can be compared with each other as patterns
class PatEq (t1 :: Nat -> Type) (t2 :: Nat -> Type) where
    patEq :: t1 n1 -> t2 n2 -> Maybe (Size t1 :~: Size t2)


----------------------------------------------------------
-- Pattern binding (N-ary binding)
----------------------------------------------------------

-- The `PatBind` type generalizes the definitions above
-- to bind (Size p) variables.
-- Patterns can also include free occurrences of variables so
-- they are also indexed by a scope level.
-- As in `Bind` above, this data structure includes a delayed
-- substitution for the variables in the body of the binder.
data PatBind v c (pat :: Nat -> Type) (n :: Nat) where
  PatBind ::
    pat n ->
    Env v m n ->
    c (Plus (Size pat) m) ->
    PatBind v c pat n

-- | Create a `PatBind` with an identity substitution.
patBind ::
  forall v c pat n.
  (Sized pat, Subst v c) =>
  pat n ->
  c (Plus (Size pat) n) ->
  PatBind v c pat n
patBind pat = PatBind pat idE

-- | Access the pattern of a pattern binding
getPat :: PatBind v c pat n -> pat n
getPat (PatBind pat env t) = pat

-- | Access the body of a pattern binding.
-- The pattern type determines the number of variables
-- bound in the pattern
getBody ::
  forall v c pat n.
  (Sized pat, Subst v v, Subst v c) =>
  PatBind v c pat n ->
  c (Plus (Size pat) n)
getBody (PatBind (pat :: pat n) (env :: Env v m n) t) =
  applyE @v @c @(Plus (Size pat) m) (upN (size pat) env) t

unPatBind ::
  forall v c pat n d.
  (SNatI n, Sized pat, Subst v v, Subst v c) =>
  PatBind v c pat n ->
  (forall m. (SNatI m, m ~ Plus (Size pat) n) => pat n -> c m -> d) ->
  d
unPatBind bnd f =
  withSNat (sPlus (size (getPat bnd)) (snat @n)) $
    f (getPat bnd) (getBody bnd)

-- | Apply a function to the pattern, suspended environment and body
-- in a pattern binding
unPatBindWithEnv ::
  (Sized pat, SubstVar v) =>
  PatBind v c pat n ->
  (forall m. pat n -> Env v m n -> c (Plus (Size pat) m) -> d) ->
  d
unPatBindWithEnv (PatBind pat r t) f = f pat r t

instantiatePat ::
  forall v c pat n.
  (Sized pat, Subst v c) =>
  PatBind v c pat n ->
  Env v (Size pat) n ->
  c n
instantiatePat b e =
  unPatBindWithEnv
    b
    (\p r t -> withSNat (size p) $ applyE (e .++ r) t)

applyPatUnder ::
  (forall n. Sized pat, Subst v v, Subst v c, Subst v pat) =>
  (forall m n. Env v m n -> c m -> c n) ->
  Env v n1 n2 ->
  PatBind v c pat n1 ->
  PatBind v c pat n2
applyPatUnder f r2 (PatBind p r1 t) =
  PatBind p' idE (f r' t)
  where
    r' = upN (size p') (r1 .>> r2)
    p' = applyE r2 p

instantiatePatWith ::
  (Sized pat, SubstVar v) =>
  (forall m n. Env v m n -> c m -> c n) ->
  PatBind v c pat n ->
  Env v (Size pat) n ->
  c n
instantiatePatWith f b v =
  unPatBindWithEnv b (\p r e -> withSNat (size p) $ f (v .++ r) e)

-----------------------------------------------------------------
-- instances for PatBind
-----------------------------------------------------------------

instance (Subst v p, Subst v v) => Subst v (PatBind v c p) where
  applyE env1 (PatBind p env2 m) =
    PatBind (applyE env1 p) (env2 .>> env1) m


instance
  ( Subst v v,
    Subst v c,
    Sized p,
    FV p,
    FV c
  ) =>
  FV (PatBind v c p)
  where
  appearsFree n b =
    let pat = getPat b
     in appearsFree n pat
          || appearsFree (shiftN (size pat) n) (getBody b)

instance
  (Sized p, SubstVar v, Subst v v, Subst v c, Strengthen c, Strengthen p) =>
  Strengthen (PatBind v c p)
  where
  strengthen' (m :: SNat m) (n :: SNat n) b =
    case axiomM @m @(Size p) @n of
      Refl ->
        case strengthen' m n (getPat b) of
          Just p' -> patBind p' <$> strengthen' m (sPlus (size (getPat b)) n) (getBody b)
          Nothing -> Nothing