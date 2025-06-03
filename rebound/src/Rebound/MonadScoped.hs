module Rebound.MonadScoped
  ( MonadScopedReader (..),
    ScopedReader (..),
    ScopedReaderT (..),
    asksS,
  )
where

import Control.Monad.Error.Class (MonadError (..))
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.Reader (MonadReader (ask, local))
import Control.Monad.Writer (MonadWriter (..))
import Data.Kind (Type)
import Data.Nat (Nat (S))
import Data.SNat (type (+))
import Data.Vec (Vec, singleton)

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