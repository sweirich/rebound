-- | Monads supporting scopes of names

module AutoEnv.MonadScoped(
  Sized(..),
  Named(..),
  MonadScoped(..),
  Scope(..),
  emptyScope,
  extendScope,
  ScopedReader(..), 
  ScopedReaderT(..),
  withSize,
  LocalName(..),
  push
 ) where

import AutoEnv.Lib
import AutoEnv.Classes
import Data.Vec as Vec
import Data.SNat as SNat

import Control.Monad.Reader
import Control.Monad.Identity

-----------------------------------------------------------------------
-- * Scopes
-----------------------------------------------------------------------

-- | Scopes know how big they are and remember names for printing 
data Scope name n = Scope {
  scope_size  :: SNat n,       -- number of names in scope
  scope_names :: Vec n name    -- stack of names currently in scope
} deriving (Eq, Show)

-- TODO: should we represent the sequence of names in scope using 
-- a more efficient data structure than a vector? Maybe a size-indexed 
-- Data.Sequence?

emptyScope :: Scope name Z
emptyScope = Scope {
    scope_size = SZ ,
    scope_names = VNil
  }

extendScope :: forall p n name. 
  SNatI p => Vec p name -> Scope name n -> Scope name (p + n)
extendScope v s = Scope { 
    scope_size  = sPlus (snat @p) (scope_size s),
    scope_names = Vec.append v (scope_names s)
  }

instance Sized (Scope name n) where
  type Size (Scope name n) = n
  size :: Scope name n -> SNat n
  size = scope_size
instance Named name (Scope name n) where
  names :: Scope name n -> Vec n name
  names = scope_names

-----------------------------------------------------------------------
-- * MonadScoped class
-----------------------------------------------------------------------
-- | Scoped monads provide implicit access to the current scope 
-- and a way to extend that scope with a vector containing new names
class (forall n. Monad (m n)) => MonadScoped name m | m -> name where
  scope :: m n (Scope name n)
  pushVec :: SNatI p => Vec p name -> m (p + n) a -> m n a

-- | Access the current size of the scope as an implicit argument
withSize :: MonadScoped name m => (SNatI n => m n a) -> m n a
withSize f = do
  s <- scope
  withSNat (scope_size s) f


-----------------------------------------------------------------------
-- * ScopedReader monad
-----------------------------------------------------------------------

-- Trivial instance of MonadScoped
type ScopedReader name = ScopedReaderT name Identity

-----------------------------------------------------------------------
-- * ScopedReaderT monad transformer
-----------------------------------------------------------------------

-- | A monad transformer that adds a scope environment to any existing monad
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

instance MonadReader e m => MonadReader e (ScopedReaderT name m n) where
  ask = ScopedReaderT (const ask)
  local f m = ScopedReaderT (\s -> local f (runScopedReaderT m s)) 
                                       

instance Monad m =>
    MonadScoped name (ScopedReaderT name m) where
        scope = ScopedReaderT $ \s -> return s
        pushVec n m = ScopedReaderT $ \env -> runScopedReaderT m (extendScope n env)

-----------------------------------------------------------------------
-- * Named patterns
-----------------------------------------------------------------------

-- | Patterns that know the names of their binding variables
class Sized pat => Named name pat where
    names :: pat -> Vec (Size pat) name

-- Add new names to the current scope
push :: (MonadScoped name m, Named name pat) => 
  pat -> m (Size pat + n) a -> m n a
push p = withSNat (size p) $ pushVec (names p)

instance Named LocalName LocalName where
  names :: LocalName -> Vec N1 LocalName
  names ln = ln ::: VNil

instance Named name (Vec p name) where
  names :: Vec p name -> Vec p name
  names x = x

-- TODO: this isn't isn't very good... it doesn't try to 
-- "freshen" the names in any way
instance Named LocalName (SNat p) where
  names :: SNat p -> Vec p LocalName
  names p = fmap toLocalName vec where
    vec :: Vec p Int
    vec = Vec.iterateN p Prelude.succ 0
    toLocalName :: Int -> LocalName 
    toLocalName i = LocalName ("_" <> show i)
   


