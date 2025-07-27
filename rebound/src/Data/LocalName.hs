-- | A simple wrapper for strings
module Data.LocalName where

newtype LocalName = LocalName {name :: String}
  deriving (Ord)

-- All local names are equal so that when they are used as patterns 
-- they will be ignored.
instance Eq LocalName where
  x1 == x2 = True

instance Show LocalName where
  show (LocalName x) = x

internalName :: LocalName
internalName = LocalName "_internal"
