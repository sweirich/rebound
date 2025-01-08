-- Monads supporting named scopes
-- TODO: generalize this library to remember arbitrary data?
module AutoEnv.MonadScoped(
  Pat.Sized(..),
  Named(..),LocalName(..),
  MonadScoped(..),
  Scope(..),emptyScope,extendScope,
  ScopedReader(..), ScopedReaderT(..)
 ) where

import AutoEnv.Lib
import Data.Vec as Vec
import AutoEnv.Pat.Simple as Pat
import AutoEnv.LocalName

import Control.Monad.Reader
import Control.Monad.Identity


class Pat.Sized pat => Named pat where
    patLocals :: pat -> Vec (Size pat) LocalName

instance Named LocalName where
    patLocals ln = ln ::: VNil

-- Scoped monads provide implicit access to the current scope 
-- and a way to extend that scope with an arbitrary pattern
-- containing local names
class (forall n. Monad (m n)) => MonadScoped m where
  scope :: m n (Scope n)
  push  :: Named pat => pat -> m (Plus (Size pat) n) a -> m n a

-- Scopes know how big they are and remember local names for printing 
data Scope n = Scope { 
  scope_size   :: SNat n,           -- number of names in scope
  scope_locals :: Vec n LocalName   -- stack of names currently in scope
}

emptyScope :: Scope Z
emptyScope = Scope { 
    scope_size = SZ , 
    scope_locals = VNil 
  } 

extendScope :: Named pat => pat -> Scope n -> Scope (Plus (Size pat) n)
extendScope pat s = 
   Scope { scope_size = sPlus (Pat.size pat) (scope_size s),
           scope_locals = Vec.append (patLocals pat) (scope_locals s) 
         }

-- Trivial instance of a MonadScoped
type ScopedReader = ScopedReaderT Identity

-- Monad transformer that adds a scope environment to any existing monad
-- This is the Reader monad containing a Scope

newtype ScopedReaderT m n a = 
    ScopedReaderT { runScopedReaderT :: Scope n -> m a }
       deriving (Functor)

instance Applicative m => Applicative (ScopedReaderT m n) where
    pure f = ScopedReaderT $ \x -> pure f
    ScopedReaderT f <*> ScopedReaderT x = ScopedReaderT (\e -> f e <*> x e)

instance Monad m => Monad (ScopedReaderT m n) where
    ScopedReaderT m >>= k = ScopedReaderT $ \e -> 
        m e >>= (\v -> let x = k v in runScopedReaderT x e)

instance Monad m => 
    MonadScoped (ScopedReaderT m) where
        scope = ScopedReaderT $ \s -> return s
        push n m = ScopedReaderT $ \env -> runScopedReaderT m (extendScope n env)
     
