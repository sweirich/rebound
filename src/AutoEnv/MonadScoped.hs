-- Monads supporting named scopes

{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FunctionalDependencies #-}
module AutoEnv.MonadScoped(
  Sized(..),
  Named(..),LocalName(..),
  MonadScoped(..),
  Scope(..),emptyScope,extendScope,
  ScopedReader(..), ScopedReaderT(..),
  withSize
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
  push  :: Named name pat => pat -> m (Size pat + n) a -> m n a

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

extendScope :: Named name pat => pat -> Scope name n -> Scope name (Size pat + n)
extendScope pat s = 
   Scope { scope_size = sPlus (size pat) (scope_size s),
           scope_names = Vec.append (names pat) (scope_names s) 
         }

-- Trivial instance of a MonadScoped
type ScopedReader name = ScopedReaderT name Identity

-- Monad transformer that adds a scope environment to any existing monad
-- This is the Reader monad containing a Scope

newtype ScopedReaderT name m n a = 
    ScopedReaderT { runScopedReaderT :: Scope name n -> m a }
       deriving (Functor)

instance Applicative m => Applicative (ScopedReaderT name m n) where
    pure f = ScopedReaderT $ \x -> pure f
    ScopedReaderT f <*> ScopedReaderT x = ScopedReaderT (\e -> f e <*> x e)

instance Monad m => Monad (ScopedReaderT name m n) where
    ScopedReaderT m >>= k = ScopedReaderT $ \e -> 
        m e >>= (\v -> let x = k v in runScopedReaderT x e)

instance Monad m => 
    MonadScoped name (ScopedReaderT name m) where
        scope = ScopedReaderT $ \s -> return s
        push n m = ScopedReaderT $ \env -> runScopedReaderT m (extendScope n env)
     

