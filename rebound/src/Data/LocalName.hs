-- |
-- Module      : Data.LocalName
-- Description : Strings with an "identity" equality
module Data.LocalName where

import Test.QuickCheck

-- | A simple wrapper for strings
-- All local names are *equal* so that when they are used as patterns
-- they will be ignored.
newtype LocalName = LocalName {name :: String}

instance Eq LocalName where
  x1 == x2 = True

rawEq :: LocalName -> LocalName -> Bool
rawEq n1 n2 = name n1 == name n2

instance Show LocalName where
  show (LocalName x) = x

-- | A default name
internalName :: LocalName
internalName = LocalName "_internal"

wildcardName :: LocalName
wildcardName = LocalName "_"

instance Arbitrary LocalName where
  arbitrary = do 
    str <- elements [ "x", "y", "z", "w" ]
    num <- elements [1,2,3,4,5,0]
    return (LocalName (str ++ show num))