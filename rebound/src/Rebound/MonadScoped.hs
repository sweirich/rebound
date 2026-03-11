-- |
-- Description: Scoped variants of some monads
--
-- Provides scoped variants of monads from [mtl](https://hackage.haskell.org/package/mtl).

module Rebound.MonadScoped
  ( MonadScopedReader (..),
    ScopedReader (..),
    ScopedReaderT (..),
    asksS,
    runScopedReader,
    MonadScopedState (..),
    ScopedState (..),
    ScopedStateT (..),
    evalScopedState,
    evalScopedStateT,
    execScopedState,
    execScopedStateT,
    modifyS,
    getsS
  )
where

import Control.Monad (liftM2, (>=>))
import Control.Monad.Error.Class (MonadError (..))
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.Reader (MonadReader (ask, local), asks)
import Control.Monad.Writer (MonadWriter (..))
import Data.Kind (Type)
import Data.Nat (Nat (S))
import Data.SNat (type (+))

-----------------------------------------------------------------------
-- Reader class
-----------------------------------------------------------------------

-- | Scoped variant of 'Control.Monad.Reader.MonadReader'.
--
-- __Note__: the "environment" mentioned here as nothing to do with 'Rebound.Env.Env'!
class (forall n. Monad (m n)) => MonadScopedReader e m | m -> e where
  {-# MINIMAL (askS | readerS), localS #-}
  -- | Retrieve the environment.
  askS :: m n (e n)
  askS = readerS id
  -- | Run a function in an altered environment.
  localS :: (e n -> e n') -> m n' a -> m n a
  -- | Retrieve a function of the environment.
  readerS :: (e n -> a) -> m n a
  readerS f = f <$> askS

-- | Retrieve the environment.
asksS :: (MonadScopedReader e m) => (e n -> a) -> m n a
asksS = readerS

-----------------------------------------------------------------------
-- Reader monad
-----------------------------------------------------------------------

-- | Computations that need a (read-only) environment.
type ScopedReader e n a = ScopedReaderT e Identity n a

-- | Run the computation with the provided environment.
runScopedReader :: ScopedReader e n a -> e n -> a
runScopedReader c m = runIdentity $ runScopedReaderT c m

-----------------------------------------------------------------------
-- Reader transformer
-----------------------------------------------------------------------

-- | A scoped variant of 'Control.Monad.Reader.ReaderT'.
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
-- State class
-----------------------------------------------------------------------

-- | Scoped variant of 'Control.Monad.State.MonadState'.
class (forall n. Monad (m n)) => MonadScopedState s m | m -> s where
  {-# MINIMAL rescope, (stateS | (getS, putS)) #-}
  -- | Change the scope of the environment, run a function, and change back the scope.
  rescope :: (s n -> s n') -> (s n' -> s n) -> m n' a -> m n a

  -- | Retrieve the state.
  getS :: m n (s n)
  getS = stateS $ \s -> (s, s)

  -- | Set the state.
  putS :: s n -> m n ()
  putS s = stateS $ const ((), s)

  -- | Lift a function into a monadic computation.
  stateS :: (s n -> (a, s n)) -> m n a
  stateS f = do
    s <- getS
    let (v, s') = f s
    putS s'
    return v

-- | Apply a function to the state.
modifyS :: (MonadScopedState s m) => (s n -> s n) -> m n ()
modifyS f = do
  s <- getS
  putS $ f s

-- | Retrieve a function of the state.
getsS :: (MonadScopedState s m) => (s n -> a) -> m n a
getsS f = f <$> getS

-----------------------------------------------------------------------
-- State monad
-----------------------------------------------------------------------

-- | Computations that need a state.
type ScopedState s n a = ScopedStateT s Identity n a

-- | Run the computation with the provided state, and return the result as well as the final state.
runScopedState :: ScopedState s n a -> s n -> (a, s n)
runScopedState m s = runIdentity $ runScopedStateT m s

-- | Run the computation with the provided state, and return the result.
evalScopedState :: ScopedState s n a -> s n -> a
evalScopedState m s = runIdentity $ evalScopedStateT m s

-- | Run the computation with the provided state, and return the final state.
execScopedState :: ScopedState s n a -> s n -> s n
execScopedState m s = runIdentity $ execScopedStateT m s

-----------------------------------------------------------------------
-- State transformer
-----------------------------------------------------------------------

-- | A scoped variant of 'Control.Monad.State.StateT'.
newtype ScopedStateT s m n a = ScopedStateT {runScopedStateT :: s n -> m (a, s n)}
  deriving (Functor)

-- | Run the computation with the provided state, and return the result.
evalScopedStateT :: (Functor m) => ScopedStateT s m n a -> s n -> m a
evalScopedStateT m s = fst <$> runScopedStateT m s

-- | Run the computation with the provided state, and return the final state.
execScopedStateT :: (Functor m) => ScopedStateT s m n a -> s n -> m (s n)
execScopedStateT m s = snd <$> runScopedStateT m s

-- A bit disappointing, but mtl does also require m to be a monad...
instance (Monad m) => Applicative (ScopedStateT s m n) where
  pure f = ScopedStateT $ \s -> pure (f, s)
  (<*>) = liftM2 (\f a -> f a)

instance (Monad m) => Monad (ScopedStateT s m n) where
  ScopedStateT m >>= k = ScopedStateT $ m >=> (\ (m', s') -> runScopedStateT (k m') s')

instance (MonadReader r m) => MonadReader r (ScopedStateT s m n) where
  ask = ScopedStateT $ \s -> asks (,s)
  local f m = ScopedStateT (local f . runScopedStateT m)

instance (MonadError e m) => MonadError e (ScopedStateT se m n) where
  throwError e = ScopedStateT $ const (throwError e)
  catchError m k = ScopedStateT $ \s -> runScopedStateT m s `catchError` (\err -> runScopedStateT (k err) s)

instance (MonadWriter w m) => MonadWriter w (ScopedStateT s m n) where
  writer w = ScopedStateT $ \s -> (,s) <$> writer w
  listen m = ScopedStateT $ \s -> (\((m, s'), w) -> ((m, w), s')) <$> listen (runScopedStateT m s)
  pass m = ScopedStateT $ \s -> pass ((\((m, r), s') -> ((m, s'), r)) <$> runScopedStateT m s)

instance (Monad m) => MonadScopedState s (ScopedStateT s m) where
  stateS f = ScopedStateT $ pure . f
  rescope up low m = ScopedStateT $ \s -> do
    (r, s') <- runScopedStateT m (up s)
    return (r, low s')