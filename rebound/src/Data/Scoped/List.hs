-- |
-- Module: Data.Scoped.List
-- Description : Scoped lists
--
-- This module defines a type of lists indexed by a scope
-- The lists are homogenous, and every type in the list must be indexed
-- by the same scope.
-- This module is intended to be imported qualified and used with the
-- OverloadedLists Haskell language extension. Many of the operations
-- in this module have the same name as prelude functions.
{-# LANGUAGE DerivingStrategies, DeriveAnyClass #-}
module Data.Scoped.List (List,
      pattern Nil, pattern (:<),
      Data.Scoped.List.uncons,
      (Data.Scoped.List.++),
      Data.Scoped.List.concat,
      Data.Scoped.List.filter,
      Data.Scoped.List.zipWith,
      Data.Scoped.List.zipWithM_,
      IsList(..),
      module Data.Scoped.Classes) where

import Data.Nat ( Nat )
import Data.Kind ( Type )
import GHC.IsList ( IsList(..) )
import GHC.Generics
import Test.QuickCheck ( Arbitrary )
import Control.DeepSeq ( NFData )
import Data.Coerce ( coerce )
import Control.Monad qualified as M
import Data.Scoped.Classes

-- | Lists where every element has type (a n)
-- Note: the @n@ is *not* the length of the list, it is a common scope
-- for all elements in the list.
newtype List a n = MkList [a n]
    deriving newtype (Eq, Ord, Read, Show, Semigroup, Monoid, Generic, Arbitrary, NFData)
    deriving anyclass (ScopedFoldable [], ScopedTraversable [],
                        ScopedFunctor [], ScopedApplicative [], ScopedMonad [])

-- | Separate the head of the list from its tail, if applicable.
uncons :: List a n -> Maybe (a n, List a n)
uncons x = case coerce x of
      [] -> Nothing
      x:xs -> Just (x,coerce xs)

{-# COMPLETE (:<), Nil #-}
-- | Pattern for the empty list.
pattern Nil :: forall a n. List a n
pattern Nil <- (uncons -> Nothing)
 where
   Nil = coerce ([] :: [a n])

-- | Pattern for a cons-ed list.
pattern (:<) :: a n -> List a n -> List a n
pattern x :< xs <- (uncons -> Just (x,xs))
  where
    x :< xs = coerce (x : coerce xs)

-- * Prelude / Control.Monad list operations

-- | See 'Prelude.++'.
(++) :: forall t n. List t n -> List t n -> List t n
(++) = coerce ((Prelude.++):: [t n] -> [t n] -> [t n])

-- | Lists flattening / Monadic join.
concat :: List (List t) n -> List t n
concat = Data.Scoped.Classes.foldr (Data.Scoped.List.++) Nil

-- | See 'Prelude.filter'.
filter :: (a n -> Bool) -> List a n -> List a n
filter f = coerce (Prelude.filter f)

-- | See 'Prelude.zipWith'.
zipWith :: (a n -> b n -> c n) -> List a n -> List b n -> List c n
zipWith f = coerce (Prelude.zipWith f)

-- | See 'Prelude.zipWithM_'.
zipWithM_ :: forall m k f1 f2 a b c n. (Applicative m)
    => (a n -> b n -> m c) -> List a n -> List b n -> m ()
zipWithM_ f = coerce (M.zipWithM_ f)

-- | A general conversion to the standard list type.
instance IsList (List v n) where
   type Item (List v n) = v n

   fromList :: [Item (List v n)] -> List v n
   fromList = coerce

   toList :: List v n -> [Item (List v n)]
   toList = coerce

-- | Enable generic programming for the `List` type
-- We can't derive the `Data.Generic1` instance for `List`
-- using newtype deriving because the kinds differ.
-- Therefore we need to write it by hand.
instance Generic1 (List a :: Nat -> Type) where
   type Rep1 (List a) =
      U1 :+: (Rec1 a :*: Rec1 (List a))

   from1 :: List a n -> Rep1 (List a) n
   from1 (MkList []) = L1 U1
   from1 (MkList (x:xs)) = R1 (Rec1 x :*: Rec1 (MkList xs))

   to1 :: Rep1 (List a) n -> List a n
   to1 (L1 U1) = MkList []
   to1 (R1 (Rec1 x :*: Rec1 (MkList xs))) = MkList (x : xs)

