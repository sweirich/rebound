-- |
-- Module: Data.Scoped.Maybe
-- Description : Scoped maybe
--
-- This module defines a Maybe type indexed by a scope
-- This module should be imported qualified. Many of the operations
-- in this module have the same name as prelude functions.
{-# LANGUAGE DeriveAnyClass #-}
module Data.Scoped.Maybe where

import Data.Nat ( Nat )
import Data.Kind ( Type )
import GHC.Generics
import GHC.Stack.Types (HasCallStack)
import Data.Maybe qualified as M
import Prelude hiding (Maybe(..), maybe)

import Data.Coerce ( coerce )
import Test.QuickCheck (Arbitrary)
import Control.DeepSeq (NFData)
import Data.Scoped.Classes

-- | 'M.Maybe' whose (hypothetical) content is scoped.
newtype Maybe a n = MkMaybe (M.Maybe (a n))
    deriving newtype (Eq, Ord, Show, Semigroup, Monoid, Generic, Arbitrary, NFData)
    deriving anyclass (ScopedFoldable M.Maybe, ScopedTraversable M.Maybe,
        ScopedFunctor M.Maybe, ScopedApplicative M.Maybe, ScopedMonad M.Maybe)

{-# COMPLETE Nothing, Just #-}
-- | Pattern for 'M.Nothing'.
pattern Nothing :: Maybe a n
pattern Nothing = MkMaybe M.Nothing

-- | Pattern for 'M.Just'.
pattern Just :: a n -> Maybe a n
pattern Just a = MkMaybe (M.Just a)

-- | See 'M.maybe'.
maybe :: b -> (a n -> b) -> Maybe a n -> b
maybe b f = coerce (M.maybe b f)

-- | See 'M.isJust'.
isJust :: forall a n. Maybe a n -> Bool
isJust = coerce (M.isJust :: M.Maybe (a n) -> Bool)

-- | See 'M.isNothing'.
isNothing :: forall a n. Maybe a n -> Bool
isNothing = coerce (M.isNothing :: M.Maybe (a n) -> Bool)

-- | See 'M.fromJust'.
fromJust :: forall a n. HasCallStack => Maybe a n -> a n
fromJust = coerce (M.fromJust :: M.Maybe (a n) -> a n)

-- | See 'M.fromMaybe'.
fromMaybe :: forall a n. a n -> Maybe a n -> a n
fromMaybe = coerce (M.fromMaybe :: a n -> M.Maybe (a n) -> a n)

-- | See 'M.maybeToList'.
maybeToList  :: forall a n. Maybe a n -> [a n]
maybeToList = coerce (M.maybeToList :: M.Maybe (a n) -> [a n])

-- | See 'M.listToMaybe'.
listToMaybe :: forall a n. [a n] -> Maybe a n
listToMaybe = coerce (M.listToMaybe :: [a n] -> M.Maybe (a n))

instance Generic1 (Maybe a :: Nat -> Type) where
   type Rep1 (Maybe a) =
      U1 :+: Rec1 a

   from1 :: Maybe a n -> Rep1 (Maybe a) n
   from1 Nothing = L1 U1
   from1 (Just x) = R1 (Rec1 x)

   to1 :: Rep1 (Maybe a) n -> Maybe a n
   to1 (L1 U1) = Nothing
   to1 (R1 (Rec1 x)) = Just x
