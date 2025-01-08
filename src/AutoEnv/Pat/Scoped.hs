-- | A "Scoped" pattern binds variables but 
-- can also include subterms that reference 
-- free variables that are already in scope.
-- This is useful for type annotations and telescopes.

-- The pattern type must have kind `Nat -> Type`

module AutoEnv.Pat.Scoped where
import AutoEnv.Lib
import AutoEnv.Classes
import AutoEnv.Env

import AutoEnv.Pat.Simple qualified as Pat

-- A scoped pattern is any type that can be made an instance of the
-- `Sized` type class below

----------------------------------------------------------
-- Sized type class for patterns
----------------------------------------------------------

-- A quantified constraint that the Scoped size is equal
-- to the nonscoped size
-- https://blog.poisson.chat/posts/2022-09-21-quantified-constraint-trick.html
class (Pat.Sized (t n), Pat.Size (t n) ~ Size t) => PatSize t n
instance (Pat.Sized (t n), Pat.Size (t n) ~ Size t) => PatSize t n

-- | Calculate the number of binding variables in the pattern
-- This number does not need to be an explicit parameter of the type
-- so that we have more flexibility about what types we can use as 
-- patterns. However, the scope of the pattern needs to be the last 
-- parameter.
class (forall n. PatSize t n) => Sized (t :: Nat -> Type) where
  type Size t :: Nat
  -- recover the size of the pattern as a dynamic term
  -- it is usually not a good idea to use this function, if it 
  -- can be avoided 
  size :: t n -> SNat (Size t)
  size = Pat.size


-- | Pairs of types that can be compared with each other as patterns
class PatEq (t1 :: Nat -> Type) (t2 :: Nat -> Type) where
    patEq :: t1 n1 -> t2 n2 -> Maybe (Size t1 :~: Size t2)

-- instance Sized t => Pat.Sized (t n) where
--  type Size t n = Size t
--  size x = size x


----------------------------------------------------------
-- Pattern binding (N-ary binding)
----------------------------------------------------------

-- The `Bind` type generalizes the definitions above
-- to bind (Size p) variables.
-- Patterns can also include free occurrences of variables so
-- they are also indexed by a scope level.
-- As in `Bind` above, this data structure includes a delayed
-- substitution for the variables in the body of the binder.
data Bind v c (pat :: Nat -> Type) (n :: Nat) where
  Bind ::
    pat n ->
    Env v m n ->
    c (Plus (Size pat) m) ->
    Bind v c pat n

-- | Create a `Bind` with an identity substitution.
bind ::
  forall v c pat n.
  (Sized pat, Subst v c) =>
  pat n ->
  c (Plus (Size pat) n) ->
  Bind v c pat n
bind pat = Bind pat idE

-- | Access the pattern of a pattern binding
getPat :: Bind v c pat n -> pat n
getPat (Bind pat env t) = pat

-- | Access the body of a pattern binding.
-- The pattern type determines the number of variables
-- bound in the pattern
getBody ::
  forall v c pat n.
  (Sized pat, Subst v v, Subst v c) =>
  Bind v c pat n ->
  c (Plus (Size pat) n)
getBody (Bind (pat :: pat n) (env :: Env v m n) t) =
  applyE @v @c @(Plus (Size pat) m) (upN (size pat) env) t

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

instantiateWith ::
  (Sized pat, SubstVar v) =>
  Bind v c pat n ->
  Env v (Size pat) n ->
  (forall m n. Env v m n -> c m -> c n) ->
  c n
instantiateWith b v f =
  unBindWith b (\p r e -> withSNat (size p) $ f (v .++ r) e)

unbind ::
  forall v c pat n d.
  (SNatI n, Sized pat, Subst v v, Subst v c) =>
  Bind v c pat n ->
  (forall m. (SNatI m, m ~ Plus (Size pat) n) => pat n -> c m -> d) ->
  d
unbind bnd f =
  withSNat (sPlus (size (getPat bnd)) (snat @n)) $
    f (getPat bnd) (getBody bnd)

-- | Apply a function to the pattern, suspended environment and body
-- in a pattern binding
unBindWith ::
  (Sized pat, SubstVar v) =>
  Bind v c pat n ->
  (forall m. pat n -> Env v m n -> c (Plus (Size pat) m) -> d) ->
  d
unBindWith (Bind pat r t) f = f pat r t



applyUnder ::
  (forall n. Sized pat, Subst v v, Subst v c, Subst v pat) =>
  (forall m n. Env v m n -> c m -> c n) ->
  Env v n1 n2 ->
  Bind v c pat n1 ->
  Bind v c pat n2
applyUnder f r2 (Bind p r1 t) =
  Bind p' idE (f r' t)
  where
    r' = upN (size p') (r1 .>> r2)
    p' = applyE r2 p



-----------------------------------------------------------------
-- instances for Bind
-----------------------------------------------------------------

instance (Subst v p, Subst v v) => Subst v (Bind v c p) where
  applyE env1 (Bind p env2 m) =
    Bind (applyE env1 p) (env2 .>> env1) m


instance
  ( Subst v v,
    Subst v c,
    Sized p,
    FV p,
    FV c
  ) =>
  FV (Bind v c p)
  where
  appearsFree n b =
    let pat = getPat b
     in appearsFree n pat
          || appearsFree (shiftN (size pat) n) (getBody b)

instance
  (Sized p, SubstVar v, Subst v v, Subst v c, Strengthen c, Strengthen p) =>
  Strengthen (Bind v c p)
  where
  strengthen' (m :: SNat m) (n :: SNat n) b =
    case axiomM @m @(Size p) @n of
      Refl ->
        withSNat n $
        case strengthen' m n (getPat b) of
          Just p' -> bind p' <$> strengthen' m (sPlus (size (getPat b)) n) (getBody b)
          Nothing -> Nothing

-----------------------------------------------------------------
-- Rebind 
---------------------------------------------------------------

data Rebind p1 p2 n where
  Rebind :: p1 n -> p2 (Plus (Size p1) n) -> Rebind p1 p2 n

instance ((forall n. PatSize p1 n), (forall m. PatSize p2 m)) => 
  Pat.Sized (Rebind p1 p2 n) where
    type Size (Rebind p1 p2 n) = Plus (Size p2) (Size p1)
    size (Rebind p1 p2) = sPlus @(Size p2) @(Size p1) (Pat.size p2) (Pat.size p1)

instance (Sized p1, Sized p2) => Sized (Rebind p1 p2) where
  type Size (Rebind p1 p2) = Plus (Size p2) (Size p1)
  size (Rebind p1 p2) = sPlus (size p2) (size p1)

instance
  (Subst v v, Sized p1, Subst v p1, Subst v p2) =>
  Subst v (Rebind p1 p2)
  where
  applyE ::
    (Subst v v, Sized p1, Subst v p2) =>
    Env v n m ->
    Rebind p1 p2 n ->
    Rebind p1 p2 m
  applyE r (Rebind p1 p2) = Rebind (applyE r p1) (applyE (upN (size p1) r) p2)


instance (Sized p1, FV p2) => FV (Rebind p1 p2) where
  appearsFree :: (Sized p1, FV p2) => Fin n -> Rebind p1 p2 n -> Bool
  appearsFree n (Rebind p1 p2) = appearsFree (shiftN (size p1) n) p2


instance (Sized p1, Strengthen p1, Strengthen p2) => Strengthen (Rebind p1 p2) where
  strengthen' ::
    forall m n p.
    SNat m ->
    SNat n ->
    Rebind p1 p2 (Plus m n) ->
    Maybe (Rebind p1 p2 n)
  strengthen' m n (Rebind p1 p2) =
    case axiomM @m @(Size p1) @n of
      Refl ->
        Rebind <$> strengthen' m n p1
          <*> strengthen' m (sPlus (size p1) n) p2

  

unRebind ::
  forall p1 p2 n c.
  (Sized p1, Sized p2, SNatI n) =>
  Rebind p1 p2 n ->
  ( ( SNatI (Size p1),
      SNatI (Size p2),
      SNatI (Plus (Size p1) n),
      Plus (Size p2) (Plus (Size p1) n) ~ Plus (Plus (Size p2) (Size p1)) n
    ) =>
    p1 n ->
    p2 (Plus (Size p1) n) ->
    c
  ) ->
  c
unRebind (Rebind p1 p2) f =
  case axiomAssoc @(Size p2) @(Size p1) @n of
    Refl ->
      withSNat (size p1) $
        withSNat (size p2) $
          withSNat (sPlus (size p1) (snat @n)) $
            f p1 p2