-- | This module provides general operations for any type that is an instance 
-- of the IsList class, in terms of the list definitions. 
-- It is useful types that are isomorphic to lists, but don't 
-- have the same kinds. If the conversion to list is not 0-cost (i.e. a newtype)
-- then these definitions will incur overhead when deferring to the list 
-- operations.
{-# LANGUAGE PatternSynonyms #-}
module Data.IsListOps where

import Prelude hiding ((++), concat, foldr) 
import Prelude qualified as P

import GHC.IsList(IsList(..))
import qualified Data.List as List
import qualified Data.Foldable as F
import qualified Control.Monad as M


-- Pattern Synonyms for matching against lists

{-# COMPLETE (:<), Nil #-}
pattern Nil :: IsList t => t
pattern Nil <- (uncons -> Nothing)
 where 
   Nil = fromList []
pattern (:<) :: IsList t => Item t -> t -> t
pattern x :< xs <- (uncons -> Just (x,xs))
  where 
    x :< xs = fromList (x : toList xs)

-- operations from Prelude/GHC.List/Data.List that are not in Data.Foldable

(++) :: IsList t => t -> t -> t
xs ++ ys = fromList (toList xs P.++ toList xs)

concat :: (IsList t, Item t ~ u, IsList u) => t -> u
concat = foldr (++) Nil

filter :: IsList t => (Item t -> Bool) -> t -> t
filter f xs = fromList (P.filter f (toList xs))

uncons :: IsList t => t -> Maybe (Item t, t)
uncons x = case toList x of 
      [] -> Nothing
      x:xs -> Just (x,fromList xs)


-- functor
map :: (IsList a, IsList b) => (Item a -> Item b) -> a -> b
map f x = fromList (List.map f (toList x))

fmap :: (IsList a, IsList b) => (Item a -> Item b) -> a -> b
fmap f x = fromList (List.map f (toList x))

-- Functions from Data.Foldable, with type signatures defined by 
-- IsList.
-- https://hackage.haskell.org/package/base-4.21.0.0/docs/Data-Foldable.html

fold :: (Monoid (Item l), IsList l) => l -> Item l
fold x = F.fold (toList x)

foldMap :: (Monoid m, IsList l) => (Item l -> m) -> l -> m
foldMap f x = F.foldMap f (toList x)

foldMap' :: (Monoid m, IsList l) => (Item l -> m) -> l -> m
foldMap' f x = F.foldMap' f (toList x)

foldr :: IsList l => (Item l -> b -> b) -> b -> l -> b
foldr f b x = F.foldr f b (toList x)

foldr' :: IsList l => (Item l -> b -> b) -> b -> l -> b
foldr' f b x = F.foldr' f b (toList x)

foldl :: IsList l => (b -> Item l -> b) -> b -> l -> b
foldl f b x = F.foldl f b (toList x)

foldl' :: IsList l => (b -> Item l -> b) -> b -> l -> b
foldl' f b x = F.foldl f b (toList x)

foldr1 :: IsList l => (Item l -> Item l -> Item l) -> l -> Item l
foldr1 f x = F.foldr1 f (toList x)

foldl1 :: IsList l => (Item l -> Item l -> Item l) -> l -> Item l
foldl1 f x = F.foldl1 f (toList x)

null :: IsList l => l -> Bool
null x = F.null (toList x)

length :: IsList l => l -> Int
length x = F.length (toList x)

elem :: (Eq (Item l), IsList l) => Item l -> l -> Bool 
elem a x = F.elem a (toList x)

maximum :: (Ord (Item l), IsList l) => l -> Item l
maximum x = F.maximum (toList x)

minimum :: (Ord (Item l), IsList l) => l -> Item l
minimum x = F.maximum (toList x)

sum :: (Num (Item l), IsList l) => l -> Item l
sum x = F.sum (toList x)

product :: (Num (Item l), IsList l) => l -> Item l
product x = F.product (toList x)

any :: IsList l => (Item l -> Bool) -> l -> Bool
any f x = F.any f (toList x)

all :: IsList l => (Item l -> Bool) -> l -> Bool
all f x = F.all f (toList x)

mapM :: (Monad m, IsList a, IsList b) => (Item a -> m (Item b)) -> a -> m b
mapM f x = fromList <$> M.mapM f (toList x)

mapM_ :: (Monad m, IsList l) => (Item l -> m b) -> l -> m ()
mapM_ f x = M.mapM_ f (toList x)

zipWithM_ :: (Applicative m, IsList l1, IsList l2) => (Item l1 -> Item l2 -> m c) -> l1 -> l2 -> m ()
zipWithM_ f x1 x2 = M.zipWithM_ f (toList x1) (toList x2)