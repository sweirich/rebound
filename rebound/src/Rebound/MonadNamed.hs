-- |
-- Description: Monads supporting scopes of names
-- Stability: experimental
--
-- This is a simplified version of 'Rebound.MonadScoped.MonadScopedReader',
-- where the environment is restricted to a vector of names.

module Rebound.MonadNamed
  ( Sized (..),
    S.MonadScopedReader,
    Scope,
    ScopedReader (..),
    ScopedReaderT (..),
    scope,
    pushVec,
    push,
    LocalName (..),
    runScopedReader,
    runScopedReaderT,
  )
where

import Rebound hiding (fromVec)
import Data.SNat as SNat
import Data.Vec as Vec
import qualified Rebound.MonadScoped as S
import Rebound.MonadScoped (MonadScopedReader(..))
import Data.LocalName

-----------------------------------------------------------------------
-- Scopes
-----------------------------------------------------------------------

-- | A mapping from variables in scope to a name.
newtype Scope name n = Scope {names :: Vec n name}
  deriving (Eq, Show)

emptyScope :: Scope name Z
emptyScope = Scope VNil

fromVec :: Vec p name -> Scope name p
fromVec v = Scope v

extendScope ::
  forall p n name.
  (SNatI p) =>
  Vec p name ->
  Scope name n ->
  Scope name (p + n)
extendScope v (Scope s) = Scope $ Vec.append v s

-----------------------------------------------------------------------
-- MonadScoped class
-----------------------------------------------------------------------

-- | Get the name of variables in scope.
scope :: MonadScopedReader (Scope name) m => m n (Vec n name)
scope = readerS names

-- | Add a new variable to the scope.
push :: (MonadScopedReader (Scope name) m)
  => name -> m (S n) a -> m n a
push n = localS (extendScope (n ::: VNil))

-- | Add a vector of new variables to the scope.
pushVec :: (MonadScopedReader (Scope name) m)
  => Vec p name -> m (p + n) a -> m n a
pushVec v = withSNat (vlength v) $ localS (extendScope v)

-----------------------------------------------------------------------
-- ScopedReader monad
-----------------------------------------------------------------------

-- | A monad transformer to keep track of the name of variables in scope.
type ScopedReaderT name m n a = S.ScopedReaderT (Scope name) m n a

-- | A monad to keep track of the name of variables in scope.
type ScopedReader name n a = S.ScopedReader (Scope name) n a

-- | Run the computation with the provided vector of names.
runScopedReaderT :: forall m n name a. ScopedReaderT name m n a -> Vec n name -> m a
runScopedReaderT c v = S.runScopedReaderT c (Scope v)

-- | Run the computation with the provided vector of names.
runScopedReader :: forall n name a. ScopedReader name n a -> Vec n name -> a
runScopedReader c v = S.runScopedReader c (Scope v)