-- | A simple wrapper for strings
-- All local names are equal so that when they are used as patterns 
-- they will be ignored.
module Data.LocalName where

newtype LocalName = LocalName {name :: String}

instance Eq LocalName where
  x1 == x2 = True

instance Show LocalName where
  show (LocalName x) = x

-- | A default name
internalName :: LocalName
internalName = LocalName "_internal"
