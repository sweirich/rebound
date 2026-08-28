{-# OPTIONS --erasure #-}

-- |
-- Module      : Rebound.Env
-- Description : Environments, or mappings from variables to terms
--
-- Environments, also called /parallel substitutions/ or
-- /multi-substitutions/, map all variables in a scope to terms in
-- another scope.
--
-- The representation is the one rebound uses by default,
-- @Rebound.Env.Lazy@: a "defunctionalized" environment, where every
-- operation that could be expensive gets its own constructor and is
-- carried out only when a variable is finally looked up.  Stored values
-- are lazy, the rest of the environment is strict, composition of an
-- @Inc@ with a @Cons@ cancels, and the empty environment is optimized
-- away (Wadler).
--
-- ERASURE: the two scopes of an @Env@ are marked @\@0@, exactly as they
-- are erased in Haskell.  The amounts stored in @Weak@ and @Inc@ are
-- /not/: we compute with them, so they must survive to runtime.
--
-- Haskell cannot draw that line.  A type-level @m@ is always erased, so
-- rebound has to store an @SNat m@ alongside it and rely on the two
-- agreeing.  Here the single un-annotated @Nat@ plays both roles: it is
-- the index in the type and the number in the code.
--
-- Other differences from the Haskell:
--
--   * Haskell's @Subst@ / @SubstVar@ classes become Agda records used as
--     instance arguments.
--
--   * 'comp' reaches its two-argument optimizations by splitting the
--     shift amount on the left first; see the note there.
module Rebound.Env where

open import Rebound.Lib
open import Data.Fin using (absurd; weakenFin)

------------------------------------------------------------------------
-- * Substitution class declarations
------------------------------------------------------------------------

-- | Well-scoped types that can be the range of an environment.  @var@
-- should generally be the @Var@ constructor from the syntax.
record SubstVar (v : @0 Nat → Set) : Set where
  field
    var : ∀ {@0 n} → Fin n → v n
open SubstVar {{...}} public

------------------------------------------------------------------------
-- * Environment representation
------------------------------------------------------------------------

-- | Maps variables in scope @n@ to terms (of type @a@) in scope @m@.
--
-- Every constructor is a suspended operation: @Weak@ raises the bound
-- without touching any variable, @Inc@ shifts every variable, @Cons@
-- extends, and @_:<>_@ composes.  Nothing happens until 'applyEnv'
-- reaches a variable.
-- | The left-hand side of a suspended composition.
--
-- Haskell's @(:<>)@ takes two arbitrary environments, but the only
-- compositions the library ever suspends have a @Weak@ or an @Inc@ on
-- the left -- both of which map variables to variables.  Recording that
-- in the type is what lets 'applyEnv' below need no `Subst` instance:
-- a renaming can be pushed through a lookup without substituting.
data Ren : @0 Nat → @0 Nat → Set where
  RWeak : ∀ {@0 n} (m : Nat) → Ren n (m + n)
  RInc  : ∀ {@0 n} (m : Nat) → Ren n (m + n)

applyRen : ∀ {@0 n m} → Ren n m → Fin n → Fin m
applyRen (RWeak m) x = weakenFin m x
applyRen (RInc  m) x = shiftN m x

infixr 9 _:<>_
data Env (a : @0 Nat → Set) : @0 Nat → @0 Nat → Set where
  Zero  : ∀ {@0 n}     → Env a Z n
  Weak  : ∀ {@0 n}     (m : Nat) → Env a n (m + n)  -- weaken range by m
  Inc   : ∀ {@0 n}     (m : Nat) → Env a n (m + n)  -- shift range by m
  Cons  : ∀ {@0 m n}   → a m → Env a n m → Env a (S n) m
  _:<>_ : ∀ {@0 m n p} → Ren m n → Env a n p → Env a m p

------------------------------------------------------------------------
-- * Applying an environment to a term
------------------------------------------------------------------------

-- | Apply the environment throughout a term of type @c n@, replacing
-- variables with values of type @v m@.
record Subst (v c : @0 Nat → Set) : Set where
  field
    applyE : ∀ {@0 n m} → Env v n m → c n → c m
open Subst {{...}} public

private
  variable
    @0 m n p : Nat
    a b c v : @0 Nat → Set

-- | Increment all free variables in a term by @k@.
weaken : {{_ : Subst a a}} (k : Nat) → a n → a (k + n)
weaken k t = applyE (Inc k) t

-- | The value of index @x@ in the environment.  This is where the
-- suspended operations are finally carried out.
--
-- Because a suspended composition stores a renaming, this is a plain
-- structural recursion on the environment: no `Subst` instance, and so
-- no hidden call back into the client's `applyE`.  Agda accepts it
-- outright, and the acceptance means something.
applyEnv : {{_ : SubstVar a}} → Env a n m → Fin n → a m
applyEnv Zero       ()
applyEnv (Weak m)   x      = var (weakenFin m x)
applyEnv (Inc m)    x      = var (shiftN m x)
applyEnv (Cons t s) FZ     = t
applyEnv (Cons t s) (FS x) = applyEnv s x
applyEnv (ρ :<> s)  x      = applyEnv s (applyRen ρ x)

-- | An optimized version of 'applyE': check whether we are applying an
-- identity environment first.
--
-- Haskell takes the traversal as an argument so that the same
-- optimization can be reused by the generic (@GHC.Generics@) code path.
-- Here it is simpler to resolve the instance directly.
applyOpt : {{_ : Subst v c}}
         → Env v n m → c n → c m
applyOpt (Inc Z)  x = x
applyOpt (Weak Z) x = x
applyOpt r        x = applyE r x

------------------------------------------------------------------------
-- * Construction and modification
------------------------------------------------------------------------

-- | The empty environment (zero domain).
zeroE : Env a Z n
zeroE = Zero

-- | Increase the bound on free variables (on the left), without
-- changing any free variable.
weakenE' : (m : Nat) → Env a n (m + n)
weakenE' = Weak

-- | Shift the term, increasing every free variable as well as the bound
-- by the provided amount.
shiftNE : (m : Nat) → Env a n (m + n)
shiftNE = Inc

shift1E : Env a n (S n)
shift1E = shiftNE 1

-- | The identity environment: does not modify the scope.
idE : Env a n n
idE = Inc 0

-- | @cons@ an environment, adding a new mapping for index @0@.
-- Haskell calls this @(.:)@; @.@ may not appear in an Agda identifier.
infixr 5 _∷_
_∷_ : a m → Env a n m → Env a (S n) m
_∷_ = Cons

-- | A singleton environment (single index domain).
oneE : a n → Env a (S Z) n
oneE v = v ∷ zeroE

-- | Maps index 0 to the given term and every other index to itself.
singletonE : a n → Env a (S n) n
singletonE v = v ∷ idE

------------------------------------------------------------------------
-- * Composition
------------------------------------------------------------------------

-- | Compose two environments, applying them in sequence (left then
-- right).  Haskell calls this @(.>>)@.
--
-- Some of the applied optimizations are:
--
--   * identity environments (e.g. @shiftNE 0@) are eliminated;
--   * absorbing environments on the left ('zeroE') are eliminated;
--   * compatible environments are fused (two @Weak@s, two @Inc@s);
--   * an @Inc@ cancels against a @Cons@.
--
-- Agda's coverage checker cannot split the second environment while the
-- first leaves the shared scope index open, so every clause that
-- inspects both arguments splits the shift amount on the left first.
-- That turns the shared index into @S _@, which is enough to rule out
-- the impossible cases on the right.  Anything not matched falls through
-- to a suspended @_:<>_@, which is what that constructor is for.
comp : {{_ : SubstVar a}} {{_ : Subst a a}}
     → Env a m n → Env a n p → Env a m p
-- an empty environment stays empty
comp Zero          s2          = Zero
-- identities on the left
comp (Weak Z)      s2          = s2
comp (Inc Z)       s2          = s2
-- weakening fuses with weakening
comp {a = a} {m = m} (Weak (S k1)) (Weak k2) =
  subst (Env a m) (sym (axiomAssoc {k2} {S k1} {m})) (Weak (k2 + S k1))
comp (Weak (S k1)) (Inc Z)     = Weak (S k1)
comp (Weak (S k1)) s2          = RWeak (S k1) :<> s2
-- shifting fuses with shifting, and cancels against a cons
comp {a = a} {m = m} (Inc (S k1)) (Inc k2) =
  subst (Env a m) (sym (axiomAssoc {k2} {S k1} {m})) (Inc (k2 + S k1))
comp (Inc (S k1))  (Weak Z)    = Inc (S k1)
comp (Inc (S k1))  (Cons t s2) = comp (Inc k1) s2
comp (Inc (S k1))  s2          = RInc (S k1) :<> s2
-- cons distributes
comp (Cons t s1)   s2          = Cons (applyE s2 t) (comp s1 s2)
-- composition reassociates
comp (ρ :<> s2)    s3          = ρ :<> comp s2 s3

infixr 9 _>>>_
_>>>_ : {{_ : SubstVar a}} {{_ : Subst a a}}
      → Env a m n → Env a n p → Env a m p
_>>>_ = comp

------------------------------------------------------------------------
-- * Going under binders
------------------------------------------------------------------------

-- | Adapt an environment to go under a binder: the new variable maps to
-- itself, all others are shifted into the extended scope.
up : {{_ : SubstVar a}} {{_ : Subst a a}}
   → Env a m n → Env a (S m) (S n)
up (Inc Z)  = Inc Z
up (Weak Z) = Weak Z
up e        = var f0 ∷ comp e (Inc 1)

-- | Go under @p@ binders, when @p@ is a number we still have.
upNat : {{_ : SubstVar a}} {{_ : Subst a a}}
      → (p : Nat) → Env a m n → Env a (p + m) (p + n)
upNat Z     e = e
upNat (S p) e = up (upNat p e)

-- | Go under @Size pat@ binders, where the count has been erased.
--
-- Haskell needs an induction combinator (and a newtype to make the
-- motive explicit) because it cannot recurse on a type-level @p@; it
-- recurses on an @SNat p@ instead.  With @p@ erased we owe the same
-- witness, but unpacking it is the whole story: matching @⟨ k , Refl ⟩@
-- names the runtime copy and rewrites the index to it, and 'upNat' then
-- recurses on an ordinary number.
upN : {{_ : SubstVar a}} {{_ : Subst a a}}
    → Singleton p → Env a m n → Env a (p + m) (p + n)
upN ⟨ p , Refl ⟩ = upNat p

-- | Rename, then increment by 1.
skip : {{_ : SubstVar a}} {{_ : Subst a a}}
     → Env a m n → Env a m (S n)
skip e = comp e shift1E

------------------------------------------------------------------------
-- * Taking environments apart
------------------------------------------------------------------------

-- | Access the term at index 0.
head : {{_ : SubstVar a}} → Env a (S n) m → a m
head f = applyEnv f FZ

-- | @uncons@ an environment, removing the mapping for index @0@.
tail : {{_ : SubstVar a}} {{_ : Subst a a}}
     → Env a (S n) m → Env a n m
tail x = comp (shiftNE 1) x

------------------------------------------------------------------------
-- * Appending
------------------------------------------------------------------------

-- | Append two environments, when the length of the first is a number we
-- still have.
appendNat : {{_ : SubstVar a}} {{_ : Subst a a}}
          → (p : Nat) → Env a p n → Env a m n → Env a (p + m) n
appendNat Z     e1 e2 = e2
appendNat (S p) e1 e2 = head e1 ∷ appendNat p (tail e1) e2

-- | Append two environments, with the (erased) length of the first
-- supplied as a runtime witness.
appendE : {{_ : SubstVar a}} {{_ : Subst a a}}
        → Singleton p → Env a p n → Env a m n → Env a (p + m) n
appendE ⟨ p , Refl ⟩ = appendNat p

-- | Append two environments.  Haskell writes this as @(.++)@ with an
-- @SNatI p@ constraint to recover the length of the first environment
-- at runtime.
--
-- ERASURE: with @p@ erased, Agda needs the very same witness, for the
-- very same reason.  It needs no separate class to carry it, though: a
-- 'Singleton' is already a record, so it can be an instance argument
-- directly.
infixr 5 _++_
_++_ : {{_ : SubstVar a}} {{_ : Subst a a}} {{s : Singleton p}}
     → Env a p n → Env a m n → Env a (p + m) n
_++_ {{s = s}} = appendE s

------------------------------------------------------------------------
-- * Conversions
------------------------------------------------------------------------

fromVec : Vec (a n) m → Env a m n
fromVec VNil       = zeroE
fromVec (x ::: vs) = x ∷ fromVec vs

toVecNat : {{_ : SubstVar a}} {{_ : Subst a a}}
         → (m : Nat) → Env a m n → Vec (a n) m
toVecNat Z     r = VNil
toVecNat (S m) r = head r ::: toVecNat m (tail r)

toVec : {{_ : SubstVar a}} {{_ : Subst a a}}
      → Singleton m → Env a m n → Vec (a n) m
toVec ⟨ m , Refl ⟩ = toVecNat m

-- | Map over the range of an environment, preserving the scope.
transform : (∀ {@0 p} → a p → b p) → Env a n m → Env b n m
transform f Zero        = Zero
transform f (Weak x)    = Weak x
transform f (Inc x)     = Inc x
transform f (Cons t r)  = Cons (f t) (transform f r)
transform f (ρ :<> r2)  = ρ :<> transform f r2

------------------------------------------------------------------------
-- * Shiftable
------------------------------------------------------------------------

-- | Bring a scoped type into a new, bigger scope by shifting variables.
record Shiftable (t : @0 Nat → Set) : Set where
  field
    shift : ∀ {@0 n} (k : Nat) → t n → t (k + n)
open Shiftable {{...}} public

shiftFromApplyE : ∀ {v c} {{_ : Subst v c}} → ∀ {@0 n} (k : Nat) → c n → c (k + n)
shiftFromApplyE {v} k t = applyE {v} (shiftNE k) t
