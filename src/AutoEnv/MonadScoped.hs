-- Monads supporting named scopes
-- TODO: generalize this library to remember arbitrary data?
module AutoEnv.MonadScoped(
  Sized(..),
  Named(..),LocalName(..),
  MonadScoped(..),
  Scope(..),emptyScope,extendScope,
  ScopedReader(..), ScopedReaderT(..)
 ) where

import AutoEnv.Lib
import AutoEnv.Classes
import Data.Vec as Vec

import Control.Monad.Reader
import Control.Monad.Identity


class Sized pat => Named name pat where
    patLocals :: pat -> Vec (Size pat) name

instance Named LocalName LocalName where
    patLocals ln = ln ::: VNil

-- instance Named LocalName (Vec n a) where
-- patLocals v = undefined

-- Scoped monads provide implicit access to the current scope 
-- and a way to extend that scope with an arbitrary pattern
-- containing local names
class (forall n. Monad (m n)) => MonadScoped name m where
  scope :: m n (Scope name n)
  push  :: Named name pat => pat -> m (Size pat + n) a -> m n a

-- Scopes know how big they are and remember local names for printing 
data Scope name n = Scope { 
  scope_size   :: SNat n,       -- number of names in scope
  scope_locals :: Vec n name    -- stack of names currently in scope
}

emptyScope :: Scope name Z
emptyScope = Scope { 
    scope_size = SZ , 
    scope_locals = VNil 
  } 

extendScope :: Named name pat => pat -> Scope name n -> Scope name (Size pat + n)
extendScope pat s = 
   Scope { scope_size = sPlus (size pat) (scope_size s),
           scope_locals = Vec.append (patLocals pat) (scope_locals s) 
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
     

