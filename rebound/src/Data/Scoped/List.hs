-- This module defines a type of lists indexed by their scope
-- The lists are homogenous, and every type in the list must have the 
-- same scope.
-- This module is intended to be used with the OverloadedLists 
-- Haskell language extension.
{-# LANGUAGE DerivingStrategies #-}
module Data.Scoped.List (List, IsList(..),module Data.IsListOps) where

import Data.Nat
import Data.Kind
import GHC.IsList
import GHC.Generics 

import Data.IsListOps


-- | A list of scope indexed types, all with the same scope
newtype List (a :: Nat -> Type) (n :: Nat) = MkList [a n]
   deriving newtype (Eq, Ord, Read, Show, Semigroup, Monoid)
   deriving newtype (Generic)
 
-- | A general conversion to the standard list type. This enables
-- all of the operations defined in Data.IsListOps.hs
instance IsList (List v n) where
   type Item (List v n) = v n

   fromList :: [Item (List v n)] -> List v n
   fromList = MkList 
   
   toList :: List v n -> [Item (List v n)]
   toList (MkList xs) = xs

-- | Enable generic programming for the List type
-- We can't derive the Generic1 instance for List 
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

