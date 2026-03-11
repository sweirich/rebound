-- | 
-- Module       : Rebound.Bind.Scoped
-- Description  : Bind variables while referring to them
--
-- A "Scoped" pattern binds variables but can also include subterms that
-- reference free variables that are already in scope. This is useful for type
-- annotations and telescopes. The pattern type typically has kind
-- @'Nat' -> 'Type'@, the 'Nat' is used to track the (initial) number of free
-- variables. For a simpler interface, see 'Rebound.Bind.Pat.Pat'.
module Rebound.Bind.Scoped (
    module Rebound,
    Bind,
    bind,
    getPat,
    getBody,
    unbind,
    unbindl,
    instantiate,
    unbindWith,
    instantiateWith,
    applyUnder,
    instantiateWeakenEnv,

    -- * Number of binding vars in pats
    ScopedSized(..),
    scopedSize,
    scopedPatEq,
    EqSized,
    EqScopedSized,
    
    -- * Telescopes
    -- IScoped make sense, but are never used anywhere; should be remove it?
    IScopedSized,
    iscopedSize,
    iscopedPatEq,
    TeleList(..),
    lengthTele,
    nil, (<:>),(<++>),
  ) where

import Rebound
import Rebound.Bind.Pat qualified as Pat

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Maybe qualified as Maybe
import Data.Fin qualified as Fin
import Data.Vec qualified as Vec

----------------------------------------------------------
-- Sized type class for patterns
----------------------------------------------------------

-- | Constrain 'ScopedSized' to agree with 'Sized'.
class (Sized (t p), Size (t p) ~ ScopedSize t) => EqSized t p

instance (Sized (t p), Size (t p) ~ ScopedSize t) => EqSized t p

-- | Type class for the size of scoped patterns.
-- The size it returns must be the same as the one returned by 'Sized'.
--
-- This type class is there to force the size of the pattern to be independent
-- of the number of variables in scope. This technique is described by:
-- https://blog.poisson.chat/posts/2022-09-21-quantified-constraint-trick.html
class (forall p. EqSized pat p) => ScopedSized pat where
  type ScopedSize (pat :: Nat -> Type) :: Nat

-- | 'Rebound.Classes.size', but with a type referring to 'ScopedSize'.
scopedSize :: forall pat p. (ScopedSized pat) => pat p -> SNat (ScopedSize pat)
scopedSize = size

-- | Compare two patterns for equality. Provide a proof of equality of their
-- size in case of success.
scopedPatEq ::
  (ScopedSized pat1, ScopedSized pat2, PatEq (pat1 p1) (pat2 p2)) =>
  pat1 p1 ->
  pat2 p2 ->
  Maybe (ScopedSize pat1 :~: ScopedSize pat2)
scopedPatEq = patEq

-- This file uses `ScopedSize`, `scopedSize`, and `scopedNames`,
-- instead of `Size`, `size`, and `names` throughout.

----------------------------------------------------------
-- Scoped Pattern binding
----------------------------------------------------------

-- | The `Bind` type binds (ScopedSize p) variables.
-- Patterns can also include free occurrences of variables, so
-- the type is indexed by a scope level.
-- This data structure includes a delayed
-- substitution for the variables in the body of the binder.
data Bind v c (pat :: Nat -> Type) (n :: Nat) where
  Bind ::
    pat n ->
    Env v m n ->
    c (ScopedSize pat + m) ->
    Bind v c pat n

-- | To compare pattern binders, we need to unbind, but also
-- first make sure that the patterns are equal.
instance (forall n. Eq (c n), 
    PatEq (pat m n) (pat m n), 
    ScopedSized (pat m), 
    Subst v c) => Eq (Bind v c (pat m) n) where
  b1 == b2 =
    Maybe.isJust (patEq (getPat b1) (getPat b2))
      && getBody b1 == getBody b2

-- | Bind a pattern, using the identity substitution.
bind ::
  forall v c pat n.
  (ScopedSized pat, Subst v c) =>
  pat n ->
  c (ScopedSize pat + n) ->
  Bind v c pat n
bind pat = Bind pat idE

-- | Bind a pattern, while suspending the provided substitution.
bindWith ::
  (ScopedSized pat, Subst v c) =>
  pat n -> Env v m n -> c (ScopedSize pat + m) -> Bind v c pat n
bindWith = Bind

-- | Retrieve the pattern of the binding.
getPat :: Bind v c pat n -> pat n
getPat (Bind pat env t) = pat

-- | Retrieve the body of the binding.
getBody ::
  forall v c pat n.
  (ScopedSized pat, Subst v v, Subst v c) =>
  Bind v c pat n ->
  c (ScopedSize pat + n)
getBody (Bind (pat :: pat n) (env :: Env v m n) t) =
  applyE @v @c @(ScopedSize pat + m) (upN (scopedSize pat) env) t

-- | Run a function on the body (and pattern), after applying the delayed substitution.
-- The size of the (current) scope is made available at runtime.
unbind ::
  forall v c pat n d.
  (SNatI n, forall n. ScopedSized pat, Subst v v, Subst v c) =>
  Bind v c pat n ->
  ((SNatI (ScopedSize pat + n)) => pat n -> c (ScopedSize pat + n) -> d) ->
  d
unbind bnd f =
  withSNat (sPlus (scopedSize (getPat bnd)) (snat @n)) $
    f (getPat bnd) (getBody bnd)

-- | Retrieve the body, as well as the bound pattern.
unbindl :: (SNatI n, Subst v c, ScopedSized pat) => Bind v c pat n -> (pat n, c (ScopedSize pat + n))
unbindl bnd = (getPat bnd, getBody bnd)

-- | Instantiate the body (i.e. replace the bound variables) with the provided terms.
instantiate ::
  forall v c pat n.
  (forall n. ScopedSized pat, Subst v c) =>
  Bind v c pat n ->
  Env v (ScopedSize pat) n ->
  c n
instantiate b e =
  unbindWith
    b
    (\p r t -> withSNat (scopedSize p) $ applyE (e .++ r) t)

-- | Apply a function under the binder.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
applyUnder ::
  forall pat v c n1 n2.
  (ScopedSized pat, Subst v v, Subst v c, Subst v pat) =>
  (forall m. Env v m (ScopedSize pat + n2) -> c m -> c (ScopedSize pat + n2)) ->
  Env v n1 n2 ->
  Bind v c pat n1 ->
  Bind v c pat n2
applyUnder f r2 (Bind p r1 t) =
  Bind p' idE (f r' t)
  where
    r' = upN sp' (r1 .>> r2)
    sp' :: SNat (ScopedSize pat)
    sp' = size p'
    p' :: pat n2
    p' = applyE r2 p

-- | Run a function on the body.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
unbindWith ::
  (forall n. Sized (pat n), SubstVar v) =>
  Bind v c pat n ->
  (forall m. pat n -> Env v m n -> c (ScopedSize pat + m) -> d) ->
  d
unbindWith (Bind pat r t) f = f pat r t

-- | Instantiate the body (i.e. replace the bound variable) with the provided term.
-- The delayed substitution is __not__ applied, but is passed to the function instead.
instantiateWith ::
  (ScopedSized pat, SubstVar v) =>
  Bind v c pat n ->
  Env v (ScopedSize pat) n ->
  (forall m. Env v m n -> c m -> c n) ->
  c n
instantiateWith b v f =
  unbindWith b (\p r e -> withSNat (scopedSize p) $ f (v .++ r) e)

-- | Map variable 0 to given value, and shift everything else
-- in the environment.
instantiateWeakenEnv ::
  forall p n v c.
  (SubstVar v, Subst v v) =>
  SNat p ->
  SNat n ->
  v (p + n) ->
  Env v (S n) (p + n)
instantiateWeakenEnv p n a =
  a .: shiftNE p

-----------------------------------------------------------------
-- instances for Bind
-----------------------------------------------------------------

instance (ScopedSized pat, Subst v pat, Subst v v) => Shiftable (Bind v c pat) where
  shift = shiftFromApplyE @v

instance (ScopedSized pat, Subst v pat, Subst v v) => Subst v (Bind v c pat) where
  applyE (env1 :: Env v n m) (Bind (pat :: pat n) (env2 :: Env v m1 n) m) =
    Bind (applyE env1 pat) (env2 .>> env1) m

instance
  ( Subst v c,
    ScopedSized p,
    FV p,
    FV c
  ) =>
  FV (Bind v c p)
  where
  appearsFree n b =
    let pat = getPat b
     in appearsFree n pat
          || appearsFree (Fin.shiftN (scopedSize pat) n) (getBody b)

  freeVars :: forall n. (Subst v c, ScopedSized p, FV p, FV c) =>
     Bind v c p n -> Set (Fin n)
  freeVars b =
    let pat = getPat b
        body = getBody b
    in
       freeVars pat <> rescope (scopedSize pat) (freeVars body)


instance (ScopedSized p, SubstVar v, Subst v v, Subst v c, Strengthen c, Strengthen p) =>
  Strengthen (Bind v c p)
  where
  strengthenRec (k :: SNat k) (m :: SNat m) (n :: SNat n) bnd =
    withSNat (sPlus k (sPlus m n)) $
      unbind bnd $ \(p :: p (k + (m + n))) t' ->
        case ( axiomAssoc @(ScopedSize p) @k @(m + n),
               axiomAssoc @(ScopedSize p) @k @n
             ) of
          (Refl, Refl) ->
            let p' :: Maybe (p (k + n))
                p' = strengthenRec k m n p

                r :: Maybe (c (ScopedSize p + (k + n)))
                r = strengthenRec (sPlus (scopedSize p) k) m n t'
             in bind <$> p' <*> r

-----------------------------------------------------------------
-- Telescopes
---------------------------------------------------------------

-- Telescopes are parameterized by scoped patterns, with kinds
-- `pat :: Nat -> Nat -> Type`. For these types, we need to know
-- that the first argument is the number of binding variables,
-- (i.e. Size or ScopedSize) so we need yet *another* type class
-- to make this constraint.

-- | Constrain 'IScopedSized' to agree with 'ScopedSized'.
class (ScopedSize (t p) ~ p) => EqScopedSized t p

instance (ScopedSize (t p) ~ p) => EqScopedSized t p

-- | An indexed 'ScopedSized'.
class
  ( forall p. ScopedSized (pat p),
    forall p. EqScopedSized pat p
  ) =>
  IScopedSized pat

-- | 'Rebound.Classes.size', but with a type referring to 'IScopedSized'.
iscopedSize :: (IScopedSized pat) => pat p n -> SNat p
iscopedSize = scopedSize

-- | Compare two patterns for equality. Provide a proof of equality of their
-- size in case of success.
iscopedPatEq ::
  (IScopedSized pat1, IScopedSized pat2, PatEq (pat1 p1 n1) (pat2 p2 n2)) =>
  pat1 p1 n1 ->
  pat2 p2 n2 ->
  Maybe (p1 :~: p2)
iscopedPatEq = scopedPatEq

-- | A telescope binds a linear sequence of variables. Each variable can have
-- metadata attached, and that metadata can be indexed. Each piece of metadata
-- can refer to every variable initially in scope, as well as every variables
-- previously introduced by the telescope itself.
-- 
-- The type parameters are
-- - @p@ is the number of variables introduced by the telescope
-- - @n@ is the number of free variables for @A1@ (and @A2@ has @S n@, etc.)
--
-- We include some arithmetic properties with each constructors, so that these
-- get brought in scope when pattern matching. Smart constructors 'nil'
-- and '<:>' can be used to easily construct 'TeleList'.
data TeleList (pat :: Nat -> Nat -> Type) p n where
  TNil :: ( n + N0 ~ n) =>
    TeleList pat N0 n
  TCons ::
    ( IScopedSized pat,
      p2 + (p1 + n) ~ (p2 + p1) + n
    ) =>
    pat p1 n ->
    TeleList pat p2 (p1 + n) ->
    TeleList pat (p2 + p1) n

-- | Length of a 'TeleList'.
lengthTele :: TeleList pat p n -> Int
lengthTele TNil = 0
lengthTele (TCons _ ps) = 1 + lengthTele ps

-- | Smart constructor for 'TNil'.
nil :: forall pat n. TeleList pat N0 n
nil = case axiomPlusZ @n of Refl -> TNil

-- | Smart constructor for 'TCons'.
(<:>) ::
  forall p1 p2 pat n.
  (IScopedSized pat) =>
  pat p1 n ->
  TeleList pat p2 (p1 + n) ->
  TeleList pat (p2 + p1) n
e <:> t = case axiomAssoc @p2 @p1 @n of Refl -> TCons e t

-- | Append two telescopes.
(<++>) ::
  forall p1 p2 pat n.
  (IScopedSized pat) =>
  TeleList pat p1 n ->
  TeleList pat p2 (p1 + n) ->
  TeleList pat (p2 + p1) n
TNil <++> t = case axiomPlusZ @p2 of Refl -> t
(TCons @_ @p12 @p11 h t) <++> t' = case axiomAssoc @p2 @p12 @p11 of Refl -> h <:> (t <++> t')

infixr 9 <:>

instance IScopedSized (TeleList pat)

instance ScopedSized (TeleList pat p) where
  type ScopedSize (TeleList pat p) = p

instance Sized (TeleList pat p n) where
  type Size (TeleList pat p n) = p
  size TNil = s0
  size (TCons p1 p2) = sPlus (size p2) (iscopedSize p1)

instance (IScopedSized pat, Subst v v, forall p. Subst v (pat p)) => Shiftable (TeleList pat p) where
  shift = shiftFromApplyE @v

instance
  (IScopedSized pat, Subst v v, forall p. Subst v (pat p)) =>
  Subst v (TeleList pat p)
  where
  applyE r TNil = nil
  applyE r (TCons p1 p2) =
    applyE r p1 <:> applyE (upN (iscopedSize p1) r) p2

instance (IScopedSized pat, forall p. FV (pat p)) => FV (TeleList pat p) where
  appearsFree ::
    forall n.
    (IScopedSized pat, forall p1. FV (pat p1)) =>
    Fin n ->
    TeleList pat p n ->
    Bool
  appearsFree n TNil = False
  appearsFree n (TCons p1 p2) = appearsFree n p1 || appearsFree (Fin.shiftN (iscopedSize p1) n) p2

  freeVars :: TeleList pat p n -> Set (Fin n)
  freeVars TNil = Set.empty
  freeVars (TCons p1 p2) = freeVars p1 <> rescope (iscopedSize p1) (freeVars p2)

instance (forall p1. Strengthen (pat p1)) => Strengthen (TeleList pat p) where
  strengthenRec k m n TNil = Just nil
  strengthenRec (k :: SNat k) (m :: SNat m) (n :: SNat n) (TCons (p1 :: pat p1 (k + (m + n))) p2) =
    case ( axiomAssoc @p1 @k @(m + n),
           axiomAssoc @p1 @k @n
         ) of
      (Refl, Refl) ->
        (<:>)
          <$> strengthenRec k m n p1
          <*> strengthenRec (sPlus (iscopedSize p1) k) m n p2

instance
  (forall p1 p2 n1 n2. PatEq (pat p1 n1) (pat p2 n2), IScopedSized pat) =>
  PatEq (TeleList pat p1 n1) (TeleList pat p2 n2)
  where
  patEq TNil TNil = Just Refl
  patEq (TCons p1 p2) (TCons p1' p2')
    | Just Refl <- iscopedPatEq p1 p1',
      Just Refl <- iscopedPatEq p2 p2' =
        Just Refl
  patEq _ _ = Nothing

-----------------------------------------------------------------
-- Rebind
-- TODO: this is the binary version of a telescope.
-- Captures the left-to-right relationship between two patterns
-- without the list.
---------------------------------------------------------------
{-
data Rebind p1 p2 n where
  Rebind ::
    Plus (Size (p2 n)) (Plus (Size (p1 n)) n) ~ Plus (Plus (Size (p2 n)) (Size (p1 n))) n =>
    p1 n -> p2 (Plus (Size (p1 n)) n) -> Rebind p1 p2 n

rebind :: forall p1 p2 n. p1 n -> p2 (Plus (Size (p1 n)) n) -> Rebind p1 p2 n
rebind p1 p2 =
  case axiomAssoc @(Size (p2 n)) @(Size (p1 n)) @n of
    Refl -> Rebind p1 p2

instance (ScopedSized p1, ScopedSized p2) => Sized (Rebind p1 p2 n) where
    type Size (Rebind p1 p2 n) = Plus (Size (p2 n)) (Size (p1 n))
    size (Rebind p1 p2) = sPlus @(Size (p2 n)) @(Size (p1 n)) (size p2) (size p1)

-- instance (Sized p1, Sized p2) => Sized (Rebind p1 p2) where
--  type Size (Rebind p1 p2) = Plus (Size p2) (Size p1)
--  size (Rebind p1 p2) = sPlus (size p2) (size p1)

instance
  (Subst v v, forall n. ScopedSized p1, Subst v p1, Subst v p2) =>
  Subst v (Rebind p1 p2)
  where
  applyE ::
    (Subst v v, ScopedSized p1, Subst v p2) =>
    Env v n m ->
    Rebind p1 p2 n ->
    Rebind p1 p2 m
  applyE r (Rebind p1 p2) =
    rebind (applyE r p1) (applyE (upN (size p1) r) p2)

instance (forall n. ScopedSized p1, FV p2) => FV (Rebind p1 p2) where
  appearsFree :: (ScopedSized p1, FV p2) => Fin n -> Rebind p1 p2 n -> Bool
  appearsFree n (Rebind p1 p2) = appearsFree (shiftN (size p1) n) p2

unRebind ::
  forall p1 p2 n c.
  (ScopedSized p1, ScopedSized p2, SNatI n) =>
  Rebind p1 p2 n ->
  ( ( SNatI (Size (p1 n)),
      SNatI (Size (p2 n)),
      SNatI (Plus (Size (p1 n)) n),
      Plus (Size (p2 n)) (Plus (Size (p1 n)) n) ~ Plus (Plus (Size (p2 n)) (Size (p1 n))) n
    ) =>
    p1 n ->
    p2 (Plus (Size (p1 n)) n) ->
    c
  ) ->
  c
unRebind (Rebind p1 p2) f =
  case axiomAssoc @(Size (p2 n)) @(Size (p1 n)) @n of
    Refl ->
      withSNat (size p1) $
        withSNat (size p2) $
          withSNat (sPlus (size p1) (snat @n)) $
            f p1 p2
-}