{-# OPTIONS --erasure #-}

-- |
-- Module      : Rebound.MonadScoped
-- Description : Scope-indexed reader and state monads
--
-- Haskell states these as classes:
--
-- @
-- class (forall n. Monad (m n)) => MonadScopedReader e m | m -> e
-- class (forall n. Monad (m n)) => MonadScopedState  s m | m -> s
-- @
--
-- Both use a quantified superclass and a functional dependency, and Agda
-- has neither.  So this module ports the two concrete transformers
-- instead, specialized to the error monad the examples actually use.
-- The operations, and their meanings, are the Haskell's.
module Rebound.MonadScoped where

open import Rebound.Lib

------------------------------------------------------------------------
-- * Scope-indexed reader
------------------------------------------------------------------------

-- @ScopedReaderT e E n a@ is Haskell's @ScopedReaderT e (Except E) n a@.
ScopedReaderT : (@0 Nat → Set) → Set → @0 Nat → Set → Set
ScopedReaderT e E n a = e n → Either E a

module Reader {e : @0 Nat → Set} {E : Set} where

  infixl 1 _>>=R_ _>>R_

  returnR : ∀ {@0 n} {a : Set} → a → ScopedReaderT e E n a
  returnR x _ = Right x

  _>>=R_ : ∀ {@0 n} {a b : Set}
         → ScopedReaderT e E n a → (a → ScopedReaderT e E n b)
         → ScopedReaderT e E n b
  (m >>=R k) r with m r
  ... | Left err = Left err
  ... | Right x  = k x r

  _>>R_ : ∀ {@0 n} {a b : Set}
        → ScopedReaderT e E n a → ScopedReaderT e E n b → ScopedReaderT e E n b
  m >>R k = m >>=R λ _ → k

  throwErrorR : ∀ {@0 n} {a : Set} → E → ScopedReaderT e E n a
  throwErrorR err _ = Left err

  askS : ∀ {@0 n} → ScopedReaderT e E n (e n)
  askS r = Right r

  asksS : ∀ {@0 n} {a : Set} → (e n → a) → ScopedReaderT e E n a
  asksS f r = Right (f r)

  -- | Run a computation in a different scope.
  localS : ∀ {@0 n n'} {a : Set}
         → (e n → e n') → ScopedReaderT e E n' a → ScopedReaderT e E n a
  localS f m r = m (f r)

  runScopedReaderT : ∀ {@0 n} {a : Set} → ScopedReaderT e E n a → e n → Either E a
  runScopedReaderT m r = m r

-- | Haskell's @ScopedReader e n a = ScopedReaderT e Identity n a@: the
-- same thing with no errors.
ScopedReader : (@0 Nat → Set) → @0 Nat → Set → Set
ScopedReader e n a = e n → a

module PureReader {e : @0 Nat → Set} where

  infixl 1 _>>=P_

  returnP : ∀ {@0 n} {a : Set} → a → ScopedReader e n a
  returnP x _ = x

  _>>=P_ : ∀ {@0 n} {a b : Set}
         → ScopedReader e n a → (a → ScopedReader e n b) → ScopedReader e n b
  (m >>=P k) r = k (m r) r

  askP : ∀ {@0 n} → ScopedReader e n (e n)
  askP r = r

  asksP : ∀ {@0 n} {a : Set} → (e n → a) → ScopedReader e n a
  asksP f r = f r

  localP : ∀ {@0 n n'} {a : Set}
         → (e n → e n') → ScopedReader e n' a → ScopedReader e n a
  localP f m r = m (f r)

  runScopedReader : ∀ {@0 n} {a : Set} → ScopedReader e n a → e n → a
  runScopedReader m r = m r

------------------------------------------------------------------------
-- * Scope-indexed state
------------------------------------------------------------------------

-- @ScopedStateT s E n a@ is Haskell's @ScopedStateT s (Except E) n a@.
ScopedStateT : (@0 Nat → Set) → Set → @0 Nat → Set → Set
ScopedStateT s E n a = s n → Either E (a × s n)

module State {s : @0 Nat → Set} {E : Set} where

  infixl 1 _>>=S_ _>>S_

  returnS : ∀ {@0 n} {a : Set} → a → ScopedStateT s E n a
  returnS x st = Right (x , st)

  _>>=S_ : ∀ {@0 n} {a b : Set}
         → ScopedStateT s E n a → (a → ScopedStateT s E n b)
         → ScopedStateT s E n b
  (m >>=S k) st with m st
  ... | Left err        = Left err
  ... | Right (x , st') = k x st'

  _>>S_ : ∀ {@0 n} {a b : Set}
        → ScopedStateT s E n a → ScopedStateT s E n b → ScopedStateT s E n b
  m >>S k = m >>=S λ _ → k

  throwErrorS : ∀ {@0 n} {a : Set} → E → ScopedStateT s E n a
  throwErrorS err _ = Left err

  getS : ∀ {@0 n} → ScopedStateT s E n (s n)
  getS st = Right (st , st)

  putS : ∀ {@0 n} → s n → ScopedStateT s E n ⊤
  putS st' _ = Right (tt , st')

  getsS : ∀ {@0 n} {a : Set} → (s n → a) → ScopedStateT s E n a
  getsS f st = Right (f st , st)

  modifyS : ∀ {@0 n} → (s n → s n) → ScopedStateT s E n ⊤
  modifyS f st = Right (tt , f st)

  -- | Run a computation in a different scope, mapping the state in and
  -- back out again.
  rescope : ∀ {@0 n n'} {a : Set}
          → (s n → s n') → (s n' → s n)
          → ScopedStateT s E n' a → ScopedStateT s E n a
  rescope up low m st with m (up st)
  ... | Left err        = Left err
  ... | Right (x , st') = Right (x , low st')

  runScopedStateT : ∀ {@0 n} {a : Set}
                  → ScopedStateT s E n a → s n → Either E (a × s n)
  runScopedStateT m st = m st

  evalScopedStateT : ∀ {@0 n} {a : Set} → ScopedStateT s E n a → s n → Either E a
  evalScopedStateT m st with m st
  ... | Left err       = Left err
  ... | Right (x , _)  = Right x
