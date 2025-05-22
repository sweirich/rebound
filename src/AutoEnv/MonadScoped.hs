{-# LANGUAGE UndecidableSuperClasses #-}

module AutoEnv.MonadScoped
  ( Sized (..),
    MonadScopedReader (..),
    ScopedReader (..),
    ScopedReaderT (..),
    -- MonadScoped (..),
    -- ScopedReader (..),
    -- ScopedReaderT (..),
    -- LocalName (..),
    -- runScopedReader,
    -- scope,
    -- scopeSize,
    -- get,
    -- withScopeSize,
    -- transform,
    -- push,
    -- push1,
    -- WithData (..),
    -- pushu,
    -- push1u,
    -- WithData (..),
    -- push1,
    -- push,
  )
where

import AutoEnv.Classes (Sized (..))
import AutoEnv.Context
import AutoEnv.Env
  ( Env,
    Shiftable (..),
    Subst (..),
    SubstVar,
    applyEnv,
    fromVec,
    idE,
    oneE,
    shift1E,
    shiftNE,
    singletonE,
    weakenE',
    zeroE,
    (.++),
    (.:),
    (.>>),
  )
import AutoEnv.Lib
-- import AutoEnv.Scoped
import Control.Monad.Error.Class (MonadError (..))
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.Reader (MonadReader (ask, local))
import Control.Monad.Writer (MonadWriter (..))
-- import Data.MonoTraversable
import Data.SNat qualified as SNat
import Data.Scoped.Const (Const (..))
import Data.Vec qualified as Vec
import Prelude hiding (map)

-----------------------------------------------------------------------
-- MonadScoped class
-----------------------------------------------------------------------

-- | Scoped monads provide implicit access to the current scope and a way to
-- extend that scope with a new scope.
class (forall n. Monad (m n)) => MonadScopedReader e m | m -> e where
  {-# MINIMAL (askS | readerS), localS #-}
  askS :: m n (e n)
  askS = readerS id
  localS :: (e n -> e n') -> m n' a -> m n a
  readerS :: (e n -> a) -> m n a
  readerS f = f <$> askS

-- withScopeSize :: (MonadScopedReader e m, Sized e) => ((SNatI n) => m n a) -> m n a
-- withScopeSize k = do
--   size <- scopeSize
--   withSNat size k

asks :: (MonadScopedReader e m) => (e n -> a) -> m n a
asks = readerS

-----------------------------------------------------------------------
-- ScopedReader monad
-----------------------------------------------------------------------

-- Trivial instance of MonadScoped
type ScopedReader e n a = ScopedReaderT e Identity n a

runScopedReader c m = runIdentity $ runScopedReaderT c m

-- runScopedReader ::
--   forall t n u s b a.
--   (SubstVar s, SNatI n) =>
--   SNat n ->
--   Vec n u ->
--   Ctx s n ->
--   b n ->
--   ScopedReader u s b n a ->
--   a
-- runScopedReader n u s b m =
--   case axiomPlusZ @n of Refl -> runIdentity $ runScopedReaderT m (n, Scope u s, b)

-----------------------------------------------------------------------
-- ScopedReaderT monad transformer
-----------------------------------------------------------------------

-- | A monad transformer that adds a scope environment to any existing monad
-- We also cannot make it an instance of the MonadTrans class because
-- the scope size n needs to be the next-to-last argument instead of the
-- underlying monad
newtype ScopedReaderT e m n a = ScopedReaderT {runScopedReaderT :: e n -> m a}
  deriving (Functor)

instance (Applicative m) => Applicative (ScopedReaderT e m n) where
  pure f = ScopedReaderT $ \x -> pure f
  ScopedReaderT f <*> ScopedReaderT x = ScopedReaderT (\e -> f e <*> x e)

instance (Monad m) => Monad (ScopedReaderT e m n) where
  ScopedReaderT m >>= k = ScopedReaderT $ \e ->
    m e >>= (\v -> let x = k v in runScopedReaderT x e)

instance (MonadReader r m) => MonadReader r (ScopedReaderT e m n) where
  ask = ScopedReaderT $ const ask
  local f m = ScopedReaderT (local f . runScopedReaderT m)

instance (MonadError e m) => MonadError e (ScopedReaderT se m n) where
  throwError e = ScopedReaderT $ const (throwError e)
  catchError m k = ScopedReaderT $ \s -> runScopedReaderT m s `catchError` (\err -> runScopedReaderT (k err) s)

instance (MonadWriter w m) => MonadWriter w (ScopedReaderT e m n) where
  writer w = ScopedReaderT $ const (writer w)
  listen m = ScopedReaderT $ \s -> listen $ runScopedReaderT m s
  pass m = ScopedReaderT $ \s -> pass $ runScopedReaderT m s

instance (Monad m) => MonadScopedReader e (ScopedReaderT e m) where
  askS = ScopedReaderT return
  localS f (ScopedReaderT g) = ScopedReaderT $ g . f

-----------------------------------------------------------------------
-- Extracting data from binders/patterns
-----------------------------------------------------------------------

-- | Extract data from the pattern.
-- class (Sized p) => WithData (v :: Nat -> Type) (p :: Type) (n :: Nat) where
--   dataFold :: forall u b. (forall k. v (Size p + n) -> u k -> u (S k)) -> u b -> p -> u (Size p + b)

-- newtype Flip t a n = Flip {unflip :: t n a}
-- dataToVec :: forall n v p. (WithData v p n) => p -> Vec (Size p) (v (Size p + n))
-- dataToVec =  case axiomPlusZ @(Size p) of 
--     Refl -> unflip . dataFold @_ @_ @n c e
--   where
--     e = Flip Vec.empty
--     c h (Flip t) = Flip $ h Vec.::: t

-- pushWith :: forall n p e m v v' a. (MonadScopedReader e m, Scope v' e, WithData v p n) => (v n -> v' n) -> p -> m (Size p + n) a -> m n a
-- pushWith f p = --foldr (\v -> localS (`extend` f v)) m (dataToVec p)
--   let g = dataFold @_ @_ @_ @_ @n (push1c @(m n a)) id p
--   in error ""
--   where
--     push1c :: forall b k. v (Size p + n) -> (m k a -> b) -> (m (S k) a -> b)
--     push1c v g = g . localS (`extend` f v)

-- -- getData p = snd $ getSizedData @n p
-- -- getSizedData :: p -> (SNat (Size p), Scope u s (Size p) n)
-- -- getSizedData p = (size p, getData @n p)

-- -- instance Sized (Scope u s p n) where
-- --   type Size (Scope u s p n) = p
-- --   size (Scope v _) = Vec.vlength v

-- -- instance WithData n (Scope u s p n) u s where
-- --   getData = id
-- --   getSizedData s = (size s, s)
-- push1 :: (MonadScopedReader e m, Scope v e) => v n -> m (S n) a -> m n a
-- push1 v = localS (`extend` v)

-- push :: forall v. forall e m p n a. (MonadScopedReader e m, Scope v e, WithData v p n) => p -> m (Size p + n) a -> m n a
-- push p = localS (extendWithData @v p)

-- push1 :: forall u s b m n a. (MonadScoped u s b m, SubstVar s) => u -> s n -> m (S n) a -> m n a
-- push1 u s = pushScope (Scope.singleton u s)

-- pushu :: forall u b m n p a. (MonadScoped u Const b m, SNatI p) => Vec p u -> m (p + n) a -> m n a
-- pushu u = pushScope (Scope u mkEnv)
--   where
--     mkEnv :: forall p. (SNatI p) => Env Const p (p + n)
--     mkEnv = case snat @p of
--       SZ -> zeroE
--       SS -> Const .: (shift1E .>> mkEnv)

-- push1u :: (MonadScoped u Const b m) => u -> m (S n) a -> m n a
-- push1u u = pushu $ Vec.singleton u