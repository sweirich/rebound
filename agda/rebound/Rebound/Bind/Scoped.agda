{-# OPTIONS --erasure #-}

-- |
-- Module       : Rebound.Bind.Scoped
-- Description  : Bind variables while referring to them
--
-- A "scoped" pattern binds variables but can also include subterms that
-- reference free variables already in scope.  This is what type
-- annotations and telescopes need.  The pattern type has kind
-- @\@0 Nat -> Set@, the index tracking the (initial) number of free
-- variables.  For the simpler interface see "Rebound.Bind.Pat".
module Rebound.Bind.Scoped where

open import Rebound.Lib
open import Rebound.Classes public
open import Rebound.Env     public

------------------------------------------------------------------------
-- * Sized type class for scoped patterns
------------------------------------------------------------------------

-- | The number of variables bound by a scoped pattern.
--
-- The size must not depend on how many variables are in scope.  Haskell
-- cannot say that directly: @ScopedSize@ is an associated type of a
-- class over @pat :: Nat -> Type@, and forcing it to agree with @Size
-- (pat p)@ for /every/ @p@ needs a quantified superclass and a helper
-- class (@EqSized@) to carry it -- the trick described at
-- <https://blog.poisson.chat/posts/2022-09-21-quantified-constraint-trick.html>.
--
-- Here the independence is just where the field sits: @theScopedSize@
-- is a @Nat@ in the record, mentioning no scope at all, so there is
-- nothing to constrain.  @EqSized@ and @ScopedSized@'s superclass both
-- disappear.
record ScopedSized (pat : @0 Nat → Set) : Set where
  field
    @0 theScopedSize : Nat
    sizeOf           : ∀ {@0 n} → pat n → Singleton theScopedSize

-- | Written @ScopedSize pat@ in Haskell.
@0 ScopedSize : (pat : @0 Nat → Set) {{s : ScopedSized pat}} → Nat
ScopedSize pat {{s}} = ScopedSized.theScopedSize s

-- | The runtime witness for 'ScopedSize'.
scopedSize : {pat : @0 Nat → Set} {{s : ScopedSized pat}} {@0 n : Nat}
           → pat n → Singleton (ScopedSize pat)
scopedSize {{s}} = ScopedSized.sizeOf s

------------------------------------------------------------------------
-- * Scoped pattern binding
------------------------------------------------------------------------

-- | Binds @ScopedSize pat@ variables.  Patterns may also contain free
-- occurrences of variables, so the pattern itself is indexed by a scope.
-- The structure includes a delayed substitution for the body.
data Bind (v c : @0 Nat → Set) (pat : @0 Nat → Set) {{_ : ScopedSized pat}}
          (@0 n : Nat) : Set where
  mkBind : ∀ {@0 m} → pat n → Env v m n → c (ScopedSize pat + m) → Bind v c pat n

-- | Bind a pattern, using the identity substitution.
bind : ∀ {v c pat : @0 Nat → Set} {@0 n} {{_ : ScopedSized pat}}
     → pat n → c (ScopedSize pat + n) → Bind v c pat n
bind p t = mkBind p idE t

-- | Bind a pattern, while suspending the provided substitution.
bindWith : ∀ {v c pat : @0 Nat → Set} {@0 m n} {{_ : ScopedSized pat}}
         → pat n → Env v m n → c (ScopedSize pat + m) → Bind v c pat n
bindWith = mkBind

-- | Retrieve the pattern of the binding.
getPat : ∀ {v c pat : @0 Nat → Set} {@0 n} {{_ : ScopedSized pat}}
       → Bind v c pat n → pat n
getPat (mkBind p e t) = p

-- | Retrieve the body, applying the delayed substitution.
getBody : ∀ {v c pat : @0 Nat → Set} {@0 n} {{_ : ScopedSized pat}}
            {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
        → Bind v c pat n → c (ScopedSize pat + n)
getBody (mkBind p e t) = applyOpt (upN (scopedSize p) e) t

-- | Retrieve the body, as well as the bound pattern.
unbindl : ∀ {v c pat : @0 Nat → Set} {@0 n} {{_ : ScopedSized pat}}
             {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
        → Bind v c pat n → pat n × c (ScopedSize pat + n)
unbindl bnd = getPat bnd , getBody bnd

-- | Run a function on the body.  The delayed substitution is __not__
-- applied, but is passed to the function instead.
unbindWith : ∀ {v c pat : @0 Nat → Set} {d : Set} {@0 n} {{_ : ScopedSized pat}}
           → Bind v c pat n
           → (∀ {@0 m} → pat n → Env v m n → c (ScopedSize pat + m) → d)
           → d
unbindWith (mkBind p r t) f = f p r t

-- | Instantiate the body with the provided terms.
instantiate : ∀ {v c pat : @0 Nat → Set} {@0 n} {{_ : ScopedSized pat}}
                {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v c}}
            → Bind v c pat n → Env v (ScopedSize pat) n → c n
instantiate (mkBind p r t) e = applyOpt (appendE (scopedSize p) e r) t

-- | Instantiate the body, keeping the delayed substitution delayed.
instantiateWith : ∀ {v c pat : @0 Nat → Set} {@0 n} {{_ : ScopedSized pat}}
                    {{_ : SubstVar v}} {{_ : Subst v v}}
                → Bind v c pat n
                → Env v (ScopedSize pat) n
                → (∀ {@0 m} → Env v m n → c m → c n)
                → c n
instantiateWith b e f = unbindWith b (λ p r t → f (appendE (scopedSize p) e r) t)

-- | Apply a function under the binder.  The delayed substitution is
-- __not__ applied, but is passed to the function instead.  Note that the
-- pattern is substituted into as well -- that is what makes this
-- "scoped".
applyUnder : ∀ {v c pat : @0 Nat → Set} {@0 n1 n2} {{_ : ScopedSized pat}}
               {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v pat}}
           → (∀ {@0 m} → Env v m (ScopedSize pat + n2) → c m → c (ScopedSize pat + n2))
           → Env v n1 n2 → Bind v c pat n1 → Bind v c pat n2
applyUnder f r2 (mkBind p r1 t) =
  mkBind p' idE (f (upN (scopedSize p') (r1 >>> r2)) t)
  where p' = applyE r2 p

-- | Map variable 0 to the given value, and shift everything else.
instantiateWeakenEnv : ∀ {v} {@0 p n} → Singleton p → v (p + n) → Env v (S n) (p + n)
instantiateWeakenEnv ⟨ p , Refl ⟩ a = a ∷ shiftNE p

------------------------------------------------------------------------
-- * Instances for Bind
------------------------------------------------------------------------

-- | Substitution composes the explicit substitution with the one stored
-- at the binder, and -- unlike "Rebound.Bind.Pat" -- must also traverse
-- the pattern, since the pattern has free variables of its own.
instance
  SubstBindScoped : ∀ {v c pat : @0 Nat → Set} {{_ : ScopedSized pat}}
                      {{_ : SubstVar v}} {{_ : Subst v v}} {{_ : Subst v pat}}
                  → Subst v (Bind v c pat)
  Subst.applyE SubstBindScoped env1 (mkBind pat env2 m) =
    mkBind (applyE env1 pat) (env2 >>> env1) m

------------------------------------------------------------------------
-- * Telescopes
------------------------------------------------------------------------

-- | An indexed 'ScopedSized': patterns of kind @\@0 Nat -> \@0 Nat -> Set@
-- whose first index /is/ the number of bound variables.
--
-- Haskell needs a second helper class (@EqScopedSized@) and another
-- quantified superclass to say this; here it is one field.
record IScopedSized (pat : @0 Nat → @0 Nat → Set) : Set where
  field
    iscopedSize : ∀ {@0 p n} → pat p n → Singleton p
open IScopedSized {{...}} public

-- | A telescope binds a linear sequence of variables.  Each entry may
-- refer to every variable initially in scope, as well as to every
-- variable introduced earlier in the telescope itself.
--
--   * @p@ is the number of variables introduced by the telescope
--   * @n@ is the number of free variables for the first entry
--
-- Haskell stores an arithmetic constraint in each constructor
-- (@n + N0 ~ n@, @p2 + (p1 + n) ~ (p2 + p1) + n@) so that the equation
-- is available when pattern matching, and provides smart constructors to
-- discharge them.  Here the indices are simply as written, and the
-- equations are proved where they are needed.
data TeleList (pat : @0 Nat → @0 Nat → Set) : @0 Nat → @0 Nat → Set where
  TNil  : ∀ {@0 n} → TeleList pat N0 n
  TCons : ∀ {@0 p1 p2 n}
        → pat p1 n → TeleList pat p2 (p1 + n) → TeleList pat (p2 + p1) n

-- | The number of entries -- not the number of variables they bind.
lengthTele : ∀ {pat} {@0 p n} → TeleList pat p n → Nat
lengthTele TNil        = 0
lengthTele (TCons _ ps) = S (lengthTele ps)

infixr 9 _<:>_

nil : ∀ {pat} {@0 n} → TeleList pat N0 n
nil = TNil

_<:>_ : ∀ {pat} {@0 p1 p2 n}
      → pat p1 n → TeleList pat p2 (p1 + n) → TeleList pat (p2 + p1) n
_<:>_ = TCons

-- | Append two telescopes.
_<++>_ : ∀ {pat} {@0 p1 p2 n}
       → TeleList pat p1 n → TeleList pat p2 (p1 + n) → TeleList pat (p2 + p1) n
_<++>_ {pat} {p2 = p2} {n} TNil t =
  subst (λ q → TeleList pat q n) (sym (axiomPlusZ {p2})) t
_<++>_ {pat} {p2 = p2} {n} (TCons {p1 = p11} {p2 = p12} h t) t' =
  subst (λ q → TeleList pat q n) (sym (axiomAssoc {p2} {p12} {p11}))
        (h <:> (t <++> subst (TeleList pat p2) (sym (axiomAssoc {p12} {p11} {n})) t'))

-- | The size of a telescope, recovered by walking it.
teleSize : ∀ {pat} {{_ : IScopedSized pat}} {@0 p n} → TeleList pat p n → Singleton p
teleSize TNil          = s0
teleSize (TCons p1 p2) = sPlus (teleSize p2) (iscopedSize p1)

instance
  IScopedSizedTele : ∀ {pat} {{_ : IScopedSized pat}} → IScopedSized (TeleList pat)
  IScopedSized.iscopedSize IScopedSizedTele = teleSize

  ScopedSizedTele : ∀ {pat} {{_ : IScopedSized pat}} {@0 p} → ScopedSized (TeleList pat p)
  ScopedSizedTele {p = p} = record { theScopedSize = p ; sizeOf = teleSize }
