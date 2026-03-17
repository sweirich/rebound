module Tutorial.Top (
  module Tutorial.Scoped.Syntax,
  module Tutorial.Scoped.Gen,
  module Tutorial.Scoped.ScopeCheck,
  module Tutorial.Scoped.Eval,
  module Tutorial.Scoped.CPS,
  module Test.QuickCheck, 
  qc,
  qc100k
) where

import Tutorial.Scoped.Syntax
import Tutorial.Scoped.Gen
import Tutorial.Scoped.ScopeCheck
import Tutorial.Scoped.Eval
import Tutorial.Scoped.CPS
import Test.QuickCheck hiding (tabulate)

-- | Run quickcheck 1000 times
qc :: Testable prop => prop -> IO ()
qc = quickCheckWith stdArgs { maxSuccess = 1000 }

-- | Run quickcheck 100000 times
qc100k :: Testable prop => prop -> IO ()
qc100k = quickCheckWith stdArgs { maxSuccess = 100000 }