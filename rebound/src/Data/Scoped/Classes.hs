-- |
-- Module      : Data.Scoped.Classes
-- Description : Structures for scoped types
-- 
-- These classes provide access to scoped versions of higher-kinded classes
-- such as 'Functor'/'Foldable' etc.
-- All instances of this class should be coercible to existing instances of 
-- these classes. (Which are used in the default definitions.)

module Data.Scoped.Classes(
    type (~>)(..),
    ScopedFunctor(..),
    ScopedFoldable(..),
    ScopedTraversable(..),
    ScopedApplicative(..),
    ScopedMonad(..)
) where

import Data.Coerce
import Control.Monad as M
import Data.Kind (Type)
import GHC.Generics
import Test.QuickCheck
import Control.DeepSeq

import Data.Foldable qualified as F
import Data.Traversable qualified as T

-- | A scoped function (i.e., a function whose input & output are scoped).
newtype (~>) a b n = MkArr (a n -> b n) 
    deriving newtype (Semigroup, Monoid, Arbitrary, CoArbitrary, Testable, NFData)
    deriving stock (Generic)

-- | Scoped 'Functor'.
class (forall a n. Coercible (f a n) (k (a n)), Functor k) => ScopedFunctor k f | f -> k where
    fmap :: Functor k => (a n -> b n) -> f a n -> f b n
    fmap f = coerce (M.fmap @k f)

-- | Scoped 'Foldable'.
class (forall a n. Coercible (f a n) (k (a n)), Foldable k) => ScopedFoldable k f | f -> k where
    fold :: (Monoid (a n)) => f a n -> a n
    fold x = F.fold @k (coerce x)

    foldMap :: (Monoid m) => (a n -> m) -> f a n -> m
    foldMap f x = F.foldMap @k f (coerce x)

    foldMap' :: (Monoid m) => (a n -> m) -> f a n -> m
    foldMap' f x = F.foldMap' @k f (coerce x)

    foldr :: (a n -> b -> b) -> b -> f a n -> b
    foldr f b x = F.foldr @k f b (coerce x)

    foldr' :: (a n -> b -> b) -> b -> f a n -> b
    foldr' f b x = F.foldr' @k f b (coerce x)

    foldl ::  (b -> a n -> b) -> b -> f a n -> b
    foldl f b x = F.foldl @k f b (coerce x)

    foldl' ::  (b -> a n -> b) -> b -> f a n -> b
    foldl' f b x = F.foldl @k f b (coerce x)

    foldr1 ::  (a n -> a n -> a n) -> f a n -> a n
    foldr1 f x = F.foldr1 @k f (coerce x)

    foldl1 :: (a n -> a n -> a n) -> f a n -> a n
    foldl1 f x = F.foldl1 @k f (coerce x)

    null :: forall a n. f a n -> Bool
    null x = F.null (coerce x :: k (a n))

    length :: forall a n. f a n -> Int
    length x = F.length @k (coerce x :: k (a n))

    elem :: (Eq (a n)) => a n -> f a n -> Bool 
    elem a x = F.elem @k a (coerce x)

    maximum :: (Ord (a n)) => f a n -> a n
    maximum x = F.maximum @k (coerce x)

    minimum :: (Ord (a n)) => f a n -> a n
    minimum x = F.maximum @k (coerce x)

    sum :: (Num (a n)) => f a n -> a n
    sum x = F.sum @k (coerce x)

    product :: (Num (a n)) => f a n -> a n
    product x = F.product @k (coerce x)

    any :: (a n -> Bool) -> f a n -> Bool
    any f x = F.any @k f (coerce x)

    all :: (a n -> Bool) -> f a n -> Bool
    all f x = F.all @k f (coerce x)

    mapM_ :: (Monad m) => (a n -> m b) -> f a n -> m ()
    mapM_ f x = M.mapM_ @k f (coerce x)

-- | Scoped 'Applicative'.
class (forall a n. Coercible (t a n) (k (a n)), Applicative k) => ScopedApplicative k t | t -> k where
    pure  :: a n -> t a n
    pure x = coerce (Prelude.pure @k x) 

    (<*>) :: forall a b n. t (a ~> b) n -> t a n -> t b n  
    f <*> x = coerce (fk Prelude.<*> coerce x) where
        fk :: k (a n -> b n)
        fk = coerce <$> (coerce f :: k ((a ~> b) n))

-- | Scoped 'Monad'.
class (forall a n. Coercible (t a n) (k (a n)), Monad k, ScopedApplicative k t) => 
       ScopedMonad k t | t -> k where
    return :: a n -> t a n
    return = Data.Scoped.Classes.pure

    (>>=) :: forall a n b m. t a n -> (a n -> t b m) -> t b m
    ma >>= kb = coerce r where
        r :: k (b m)
        r = (M.>>=) (coerce ma :: k (a n)) (coerce kb)

-- The default definitions do not have 0-cost coercions due to role limitations
-- | Scoped 'Traversable'.
class (forall a n. Coercible (t a n) (k (a n)), Traversable k) => ScopedTraversable k t | t -> k where
   traverse :: forall a b n f. Applicative f => (a n -> f (b n)) -> t a n -> f (t b n)
   traverse f x = coerce <$> T.traverse @k f (coerce x)
   
   mapM :: Monad m => (a n -> m (b n)) -> t a n -> m (t b n)
   mapM f x = coerce <$> T.mapM @k f (coerce x)
   
   -- TODO ???
   -- sequenceA :: Applicative f => t (f n) -> f (t a)
   -- sequence :: Monad m => t (m a) -> m (t a)

