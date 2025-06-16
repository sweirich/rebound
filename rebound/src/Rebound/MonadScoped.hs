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

class (forall n. Monad (m n)) => MonadScopedReader e m | m -> e where
  {-# MINIMAL (askS | readerS), localS #-}
  askS :: m n (e n)
  askS = readerS id
  localS :: (e n -> e n') -> m n' a -> m n a
  readerS :: (e n -> a) -> m n a
  readerS f = f <$> askS

asksS :: (MonadScopedReader e m) => (e n -> a) -> m n a
asksS = readerS

-----------------------------------------------------------------------
-- Reader monad
-----------------------------------------------------------------------

-- Trivial instance of MonadScoped
type ScopedReader e n a = ScopedReaderT e Identity n a

runScopedReader :: ScopedReader e n a -> e n -> a
runScopedReader c m = runIdentity $ runScopedReaderT c m

-----------------------------------------------------------------------
-- Reader transformer
-----------------------------------------------------------------------

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

class (forall n. Monad (m n)) => MonadScopedState s m | m -> s where
  {-# MINIMAL rescope, (stateS | (getS, putS)) #-}
  rescope :: (s n -> s n') -> (s n' -> s n) -> m n' a -> m n a

  getS :: m n (s n)
  getS = stateS $ \s -> (s, s)
  putS :: s n -> m n ()
  putS s = stateS $ const ((), s)

  stateS :: (s n -> (a, s n)) -> m n a
  stateS f = do
    s <- getS
    let (v, s') = f s
    putS s'
    return v

modifyS :: (MonadScopedState s m) => (s n -> s n) -> m n ()
modifyS f = do
  s <- getS
  putS $ f s

getsS :: (MonadScopedState s m) => (s n -> a) -> m n a
getsS f = f <$> getS

-----------------------------------------------------------------------
-- State monad
-----------------------------------------------------------------------

type ScopedState s n a = ScopedStateT s Identity n a

runScopedState :: ScopedState s n a -> s n -> (a, s n)
runScopedState m s = runIdentity $ runScopedStateT m s

evalScopedState :: ScopedState s n a -> s n -> a
evalScopedState m s = runIdentity $ evalScopedStateT m s

execScopedState :: ScopedState s n a -> s n -> s n
execScopedState m s = runIdentity $ execScopedStateT m s

-----------------------------------------------------------------------
-- State transformer
-----------------------------------------------------------------------

newtype ScopedStateT s m n a = ScopedStateT {runScopedStateT :: s n -> m (a, s n)}
  deriving (Functor)

evalScopedStateT :: (Functor m) => ScopedStateT s m n a -> s n -> m a
evalScopedStateT m s = fst <$> runScopedStateT m s

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