module Data.Scoped.List where

import Data.Nat
import Data.Kind
import GHC.IsList
import GHC.Generics 

import qualified Data.Foldable as F
import qualified Control.Monad as M

-- A list of scope indexed types, all with the same scope
-- This module is intended to be used with the OverloadedLists 
-- Haskell language extension.

data List :: (Nat -> Type) -> Nat -> Type where
   Nil  :: List a n
   (:<) :: a n -> List a n -> List a n

deriving instance Generic1 a => Generic1 (List a)      
deriving instance Ord (a n) => Ord (List a n)
deriving instance Eq (a n) => Eq (List a n)
deriving instance Show (a n) => Show (List a n) 

instance Semigroup (List a n) where
   Nil <> l = l
   (x :< xs) <> l = x :< xs <> l
instance Monoid (a n) => Monoid (List a n) where
   mempty = Nil

-- >>> :info []
-- type List :: * -> *
-- data List a = [] | a : [a]
--   	-- Defined in ‘GHC.Types’
-- instance Generic1 [] -- Defined in ‘GHC.Generics’
-- instance MonadPlus [] -- Defined in ‘GHC.Base’
-- instance Foldable [] -- Defined in ‘Data.Foldable’
-- instance MonadFail [] -- Defined in ‘Control.Monad.Fail’
-- instance Traversable [] -- Defined in ‘Data.Traversable’
-- instance Applicative [] -- Defined in ‘GHC.Base’
-- instance Functor [] -- Defined in ‘GHC.Base’
-- instance Monad [] -- Defined in ‘GHC.Base’
-- instance IsList [a] -- Defined in ‘GHC.IsList’
-- instance Read a => Read [a] -- Defined in ‘GHC.Read’
-- instance Generic [a] -- Defined in ‘GHC.Generics’
-- instance Monoid [a] -- Defined in ‘GHC.Base’
-- instance Semigroup [a] -- Defined in ‘GHC.Base’
-- instance Show a => Show [a] -- Defined in ‘GHC.Show’
-- instance Eq a => Eq [a] -- Defined in ‘GHC.Classes’
-- instance Ord a => Ord [a] -- Defined in ‘GHC.Classes’




instance IsList (List v n) where
   type Item (List v n) = v n

   fromList :: [Item (List v n)] -> List v n
   fromList = F.foldr (:<) Nil
   
   toList :: List v n -> [Item (List v n)]
   toList Nil = []
   toList (x :< xs) = x : toList xs

fold :: (Monoid (Item l), IsList l) => l -> Item l
fold x = F.fold (toList x)

foldr :: IsList l => (Item l -> b -> b) -> b -> l -> b
foldr f b x = F.foldr f b (toList x)

null :: IsList l => l -> Bool
null x = F.null (toList x)

length :: IsList l => l -> Int
length x = F.length (toList x)

any :: IsList l => (Item l -> Bool) -> l -> Bool
any f x = F.any f (toList x)

all :: IsList l => (Item l -> Bool) -> l -> Bool
all f x = F.all f (toList x)

-- >>> :t M.mapM @[]
-- M.mapM @[] :: Monad m => (a -> m b) -> [a] -> m [b]

mapM :: (Monad m, IsList a, IsList b) => (Item a -> m (Item b)) -> a -> m b
mapM f x = fromList <$> M.mapM f (toList x)

mapM_ :: (Monad m, IsList l) => (Item l -> m b) -> l -> m ()
mapM_ f x = M.mapM_ f (toList x)

map :: (IsList l1, IsList l2) => (Item l2 -> Item l1) -> l2 -> l1
map f x = fromList (fmap f (toList x))

zipWithM_ f x1 x2 = M.zipWithM_ f (toList x1) (toList x2)