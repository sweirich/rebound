{- 

  parsing, scope checking, pretting printing, random testing 
  scope-preserving translation

-}

module Tutorial.Talk3 where


import Test.QuickCheck
import Tutorial.Scoped.Syntax
import qualified Rebound.Bind.Pat as Pat
import Data.Vec ( (!) )
import Data.Maybe as Maybe
import Tutorial.Scoped.Gen
import Tutorial.Scoped.Eval
import Tutorial.Scoped.ScopeCheck

{- ----------------------------------------------------------- -}

{- Parsing and Scope Checking

       parsing               scope checking
String ------> Named Syntax ----------------> Scoped Syntax

             injection              pretty printing
Scoped Syntax -------> Named Syntax -------------> String

-}


-- >>> parse "\\x.x"

Right tmId1 = parse "\\x.x"

-- >>> pp tmId1
-- "\\ x. x"


-- >>> parse "\\x.y"

names :: Vec N2 String
names = "y" ::: "z" ::: VNil


-- >>> parseWith names "\\x.z"

Right g = parseWith names "\\x.y"

-- >>> ppWith names g
-- "\\ x. y"


{- ----------------------------------------------------------- -}

{- QuickCheck and well-scoped/well-typed term generation -}

-- evaluating twice returns the same result
prop_eval_idempotent :: Tm Z -> Property
prop_eval_idempotent = \t ->
    discardAfter 10000 $
    case eval t of
        Just v ->
            counterexample ("v: " ++ pp v) $
            property (eval v == Just v)
        Nothing ->
            discard

{-
hci> qc (forAll0 Scoped PureLC prop_eval_idempotent)
+++ OK, passed 1000 tests; 11 discarded.
ghci> qc100k (forAll0 Scoped PureLC prop_eval_idempotent)
+++ OK, passed 100000 tests; 801 discarded.
ghci> qc100k (forAll0 Typed Full prop_eval_idempotent)
+++ OK, passed 100000 tests.
ghci> qc100k (forAll0 Scoped Full prop_eval_idempotent)
+++ OK, passed 100000 tests; 108131 discarded.
-}

-- all terms produce values (NB: this holds for well-typed terms only!)
prop_eval_exists_Val :: Tm Z -> Property
prop_eval_exists_Val = \t ->
    within 10000 $   
    case eval t of
        Just v ->
            counterexample ("not a value: " ++ pp v) $
            property (isVal v)
        Nothing ->
            counterexample ("doesn't eval") $
            property False