module AutoEnv.LocalName where
  
import AutoEnv.Lib
import AutoEnv.Pat.Simple as Pat

newtype LocalName = LocalName {name :: String}
  deriving (Eq, Ord)

instance Show LocalName where
  show (LocalName x) = x
  
internalName :: LocalName
internalName = LocalName "_internal"

instance Pat.Sized LocalName where
  type Size LocalName = N1
  size _ = s1


