-- |
-- Module       : Rebound.Bind.Pat
-- Description  : Bind variables according to a pattern
--
-- Bind variables according to a user-defined pattern.
module Rebound.Bind.Pat
  ( module Rebound,
    type Bind,
    bind,
    unbind,
    unbindl,
    getPat,
    getBody,
    instantiate,
    bindWith,
    unbindWith,
    instantiateWith,
    applyUnder,
    type Rebind (..),
    type PatList (..),
    lengthPL,
  )
where

import Rebound

import qualified Data.Fin as Fin
import qualified Data.Vec as Vec
import Data.Set (Set)
import qualified Data.Set as Set

----------------------------------------------------------
-- * Bind type
----------------------------------------------------------

-- | Type binding 'Size pat' variables.
-- This data structure includes a delayed
-- substitution for the variables in the body of the binder.
data Bind v c (pat :: Type) (n :: Nat) where
  Bind :: pat -> Env v m n -> c (Size pat + m) -> Bind v c pat n

-- | To compare pattern binders, we need to unbind, but also
-- first make sure that the patterns are equal.
instance (Eq pat, Sized pat, forall n. Eq (c n), Subst v c) => Eq (Bind v c pat n) where
  b1 == b2 =
    getPat b1 == getPat b2
      && getBody b1 == getBody b2

-- | Bind a pattern, using the identity substitution.
bind ::
  (Sized pat, Subst v c) =>
  pat ->
  c (Size pat + n) ->
  Bind v c pat n
bind pat = Bind pat idE

-- | Bind a pattern, while suspending the provided substitution.
bindWith :: pat -> Env v m n -> c (Size pat + m) -> Bind v c pat n
bindWith = Bind

-- | Retrieve the pattern of the binding.
getPat :: Bind v c pat n -> pat
getPat (Bind pat env t) = pat

-- | Retrieve the body of the binding.
getBody ::
  forall v c pat n.
  (Sized pat, Subst v c) =>
  Bind v c pat n ->
  c (Size pat + n)
getBody (Bind (pat :: pat) (env :: Env v m n) t) =
  applyOpt applyE (upN (size pat) env) t

-- | Run a function on the body (and pattern), after applying the delayed substitution.
-- The size of the (current) scope is made available at runtime.
unbind ::
  forall v c pat n d.
  (SNatI n, Sized pat, Subst v v, Subst v c) =>
  Bind v c pat n ->
  ((SNatI (Size pat + n)) => pat -> c (Size pat + n) -> d) ->
  d
unbind bnd f =
  withSNat (sPlus (size (getPat bnd)) (snat @n)) $
    f (getPat bnd) (getBody bnd)

-- | Retrieve the body, as well as the bound pattern.
unbindl :: (Sized pat, Subst v c) => Bind v c pat n -> (pat, c (Size pat + n))
unbindl bnd = (getPat bnd, getBody bnd)

-- | Instantiate the body (i.e. replace the bound variables) with the provided terms.
instantiate ::
  forall v c pat n.
  (Sized pat, Subst v c) =>
  Bind v c pat n ->
  Env v (Size pat) n ->
  c n
instantiate b e =
  unbindWith
    b
    (\p r t -> applyOpt applyE (withSNat (size p) $ e .++ r) t)

-- | Apply a function under the binder.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
applyUnder ::
  (Sized pat, Subst v c2) =>
  (forall m. Env v m (Size pat + n2) -> c1 m -> c2 (Size pat + n2)) ->
  Env v n1 n2 ->
  Bind v c1 pat n1 ->
  Bind v c2 pat n2
applyUnder f r2 (Bind p r1 t) =
  Bind p idE (f r' t)
  where
    r' = upN (size p) (r1 .>> r2)

-- | Run a function on the body.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
unbindWith ::
  (Sized pat, SubstVar v) =>
  Bind v c pat n ->
  (forall m. pat -> Env v m n -> c (Size pat + m) -> d) ->
  d
unbindWith (Bind pat (r :: Env v m n) t) f =
  f pat r t

-- | Instantiate the body (i.e. replace the bound variable) with the provided term.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
instantiateWith ::
  (Sized pat, SubstVar v) =>
  Bind v c pat n ->
  Env v (Size pat) n ->
  (forall m. Env v m n -> c m -> c n) ->
  c n
instantiateWith b v f = unbindWith b (\p r e -> withSNat (size p) $ f (v .++ r) e)

-----------------------------------------------------------------
-- instances for Bind (Subst, FV, Strengthen)
-----------------------------------------------------------------

-- | The substitution operation composes the explicit
-- substitution with the one stored at the binder
instance (SubstVar v) => Shiftable (Bind v c p) where
  shift = shiftFromApplyE @v

instance (SubstVar v) => Subst v (Bind v c p) where
  applyE :: Env v n m -> Bind v c p n -> Bind v c p m
  applyE env1 (Bind p env2 m) = Bind p (env2 .>> env1) m

instance (Subst v c, Sized p, FV c) => FV (Bind v c p) where
  appearsFree :: Fin n -> Bind v c p n -> Bool
  appearsFree n b =
    appearsFree (Fin.shiftN (size (getPat b)) n) (getBody b)
  freeVars :: forall n. Bind v c p n -> Set (Fin n)
  freeVars b = rescope (size (getPat b)) (freeVars (getBody b))


instance (Sized p, Subst v c, Strengthen c) => Strengthen (Bind v c p) where
  strengthenRec ::
    SNat k ->
    SNat m ->
    SNat n ->
    Bind v c p (k + (m + n)) ->
    Maybe (Bind v c p (k + n))
  strengthenRec (k :: SNat k) (m :: SNat m) (n :: SNat n) bnd =
    withSNat (sPlus k (sPlus m n)) $
      unbind bnd $ \(p :: p) t' ->
        case ( axiomAssoc @(Size p) @k @(m + n),
               axiomAssoc @(Size p) @k @n
             ) of
          (Refl, Refl) ->
            bind p <$> strengthenRec (sPlus (size p) k) m n t'

-----------------------------------------------------------------
-- * Rebind type
---------------------------------------------------------------

data Rebind pat p2 n where
  Rebind :: pat -> p2 (Size pat + n) -> Rebind pat p2 n

instance (SubstVar v, Sized p1, Subst v p2) => Shiftable (Rebind p1 p2) where
  shift = shiftFromApplyE @v

instance (SubstVar v, Sized p1, Subst v p2) => Subst v (Rebind p1 p2) where
  applyE :: Env v n m -> Rebind p1 p2 n -> Rebind p1 p2 m
  applyE r (Rebind p1 p2) = Rebind p1 (applyE (upN (size p1) r) p2)

instance (Sized p1, FV p2) => FV (Rebind p1 p2) where
  appearsFree :: (Sized p1, FV p2) => Fin n -> Rebind p1 p2 n -> Bool
  appearsFree n (Rebind p1 p2) = appearsFree (Fin.shiftN (size p1) n) p2

  freeVars :: (Sized p1, FV p2) => Rebind p1 p2 n -> Set (Fin n)
  freeVars = undefined

instance (Sized p1, Strengthen p2) => Strengthen (Rebind p1 p2) where
  strengthenRec (k :: SNat k) (m :: SNat m) (n :: SNat n) (Rebind (p1 :: p1) p2) =
    case ( axiomAssoc @(Size p1) @k @(m + n),
           axiomAssoc @(Size p1) @k @n
         ) of
      (Refl, Refl) ->
        Rebind p1 <$> strengthenRec (sPlus (size p1) k) m n p2

--------------------------------------------------------------
-- * Lists of patterns
--------------------------------------------------------------

-- | lists of patterns where variables at each position bind
-- later in the pattern
data PatList (pat :: Nat -> Type) p where
  PNil :: PatList pat N0
  PCons ::
    (Size (pat p1) ~ p1) =>
    pat p1 ->
    PatList pat p2 ->
    PatList pat (p2 + p1)

-- | The length of a pattern list is the number of patterns,
-- not the number of variables that it binds
lengthPL :: PatList pat p -> Int
lengthPL PNil = 0
lengthPL (PCons _ ps) = 1 + lengthPL ps

instance (forall n. Sized (pat n)) => Sized (PatList pat p) where
  type Size (PatList pat p) = p
  size PNil = s0
  size (PCons (p1 :: pat p1) (p2 :: PatList pat p2)) =
    sPlus @p2 @(Size (pat p1)) (size p2) (size p1)

instance
  (forall p1 p2. PatEq (pat p1) (pat p2)) =>
  PatEq (PatList pat p1) (PatList pat p2)
  where
  patEq :: PatList pat p1 -> PatList pat p2 -> Maybe (p1 :~: p2)
  patEq PNil PNil = Just Refl
  patEq (PCons p1 ps1) (PCons p2 ps2) = do
    Refl <- patEq p1 p2
    Refl <- patEq ps1 ps2
    return Refl
  patEq _ _ = Nothing

-- instance
--   (forall p n. WithData v (pat p) n) =>
--   WithData v (PatList pat p) n
--   where
--   extendWithData PNil = id
--   extendWithData (PCons (p1 :: pat p1') (ps :: PatList pat ps')) =
--     case axiomAssoc @ps' @p1' @n of
--       Refl -> extendWithData @v ps . extendWithData @v p1