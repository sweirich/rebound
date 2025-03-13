-- Monads supporting named scopes

{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda" #-}
module AutoEnv.MonadScoped(
  Sized(..),
  Named(..),LocalName(..),
  MonadScoped(..),
  Scope(..),emptyScope,extendScope,
  ScopedReader(..), ScopedReaderT(..),
  withSize,
  push
 ) where

import AutoEnv.Lib
import AutoEnv.Classes
import Data.Vec as Vec
import Data.SNat as SNat

import Control.Monad.Reader
import Control.Monad.Identity


class Sized pat => Named name pat where
    names :: pat -> Vec (Size pat) name

instance Named LocalName LocalName where
    names ln = ln ::: VNil

instance Named LocalName (SNat p) where
  names = go where
    go :: forall p. SNat p -> Vec p LocalName
    go SZ = VNil
    go (snat_ -> SS_ q) = LocalName ("_" <> show (SNat.succ q)) ::: go q

-- Scoped monads provide implicit access to the current scope 
-- and a way to extend that scope with an arbitrary pattern
-- containing local names
class (forall n. Monad (m n)) => MonadScoped name m | m -> name where
  scope :: m n (Scope name n)
  pushVec :: SNatI p => Vec p name -> m (p + n) a -> m n a

-- Add new names to the current scope
push :: (MonadScoped name m, Named name pat) => pat -> m (Size pat + n) a -> m n a
push p = withSNat (size p) $ pushVec (names p)

-- | Access the current size of the scope as an implicit argument
withSize :: MonadScoped name m => (SNatI n => m n a) -> m n a
withSize f = do
  s <- scope
  withSNat (scope_size s) f

-- Scopes know how big they are and remember local names for printing 
data Scope name n = Scope {
  scope_size  :: SNat n,       -- number of names in scope
  scope_names :: Vec n name    -- stack of names currently in scope
}

emptyScope :: Scope name Z
emptyScope = Scope {
    scope_size = SZ ,
    scope_names = VNil
  }

extendScope :: forall p n name. SNatI p => Vec p name -> Scope name n -> Scope name (p + n)
extendScope v s =
   Scope { scope_size  = sPlus (snat @p) (scope_size s),
           scope_names = Vec.append v (scope_names s)
         }

-- Trivial instance of a MonadScoped
type ScopedReader name = ScopedReaderT name Identity

-- Monad transformer that adds a scope environment to any existing monad
-- This is the Reader monad containing a Scope
-- However, we don't make it an instance of the MonadReader class so that 
-- the underlying monad can already be a reader.
-- We also cannot make it an instance of the MonadTrans class because 
-- the scope size n needs to be the next-to-last argument instead of the 
-- underlying monad

newtype ScopedReaderT name m n a =
    ScopedReaderT { runScopedReaderT :: Scope name n -> m a }
       deriving (Functor)

instance Applicative m => Applicative (ScopedReaderT name m n) where
    pure f = ScopedReaderT $ \x -> pure f
    ScopedReaderT f <*> ScopedReaderT x = ScopedReaderT (\e -> f e <*> x e)

instance Monad m => Monad (ScopedReaderT name m n) where
    ScopedReaderT m >>= k = ScopedReaderT $ \e ->
        m e >>= (\v -> let x = k v in runScopedReaderT x e)

-- >>> :info MonadTrans
-- type MonadTrans :: ((* -> *) -> * -> *) -> Constraint
-- class (forall (m :: * -> *). Monad m => Monad (t m)) =>
--       MonadTrans t where
--   lift :: Monad m => m a -> t m a

instance MonadReader e m => MonadReader e (ScopedReaderT name m n) where
  ask = ScopedReaderT (const ask)
  local f m = ScopedReaderT (\s -> local f (runScopedReaderT m s)) 
                                       

instance Monad m =>
    MonadScoped name (ScopedReaderT name m) where
        scope = ScopedReaderT $ \s -> return s
        pushVec n m = ScopedReaderT $ \env -> runScopedReaderT m (extendScope n env)


