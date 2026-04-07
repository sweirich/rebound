-- | Utility module for interactive us with the repl. Imports 
-- all modules of interest and provides wrappers for 
-- quickcheck that increase the number of iterations for the 
-- property 
module Tutorial.Top (

  module Tutorial.Scoped.Gen,
  module Tutorial.Scoped.ScopeCheck,
  module Tutorial.Scoped.Eval,
  module Tutorial.Scoped.CPS,
  module Test.QuickCheck, 
  qc,
  qc100k
) where

import Tutorial.Scoped.Gen
import Tutorial.Scoped.ScopeCheck hiding (testAll)
import Tutorial.Scoped.Eval hiding (testAll)
import Tutorial.Scoped.CPS hiding (testAll)
import Test.QuickCheck hiding (tabulate)

-- | Run quickcheck 1000 times
qc :: Testable prop => prop -> IO ()
qc = quickCheckWith stdArgs { maxSuccess = 1000 }

-- | Run quickcheck 100000 times
qc100k :: Testable prop => prop -> IO ()
qc100k = quickCheckWith stdArgs { maxSuccess = 100000 }