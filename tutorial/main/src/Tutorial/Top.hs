-- | Utility module for interactive us with the repl. Imports 
-- all modules of interest
module Tutorial.Top (

  module Tutorial.Scoped.Gen,
  module Tutorial.Scoped.ScopeCheck,
  module Tutorial.Scoped.Eval,
  module Tutorial.Scoped.CPS,
  module Test.QuickCheck
) where

import Tutorial.Scoped.Gen
import Tutorial.Scoped.ScopeCheck hiding (testAll)
import Tutorial.Scoped.Eval hiding (testAll)
import Tutorial.Scoped.CPS hiding (testAll)
import Test.QuickCheck hiding (tabulate)

