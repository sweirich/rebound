module DeBruijn.Skew.Suite where

import Util.Impl    
import qualified DeBruijn.Skew.SkewList
import qualified DeBruijn.Skew.ShiftList
import qualified DeBruijn.Skew.Lazy

impls :: [LambdaImpl]
impls = [ DeBruijn.Skew.SkewList.impl,
          DeBruijn.Skew.ShiftList.impl,
          DeBruijn.Skew.Lazy.impl
      ]   