module Tutorial.Simple.TestEval where

import Test.QuickCheck

import Tutorial.Simple.Syntax
import Tutorial.Simple.Eval
import Tutorial.Simple.Gen
import Tutorial.Simple.ScopeCheck

-- | The result of evaluation is a value
prop_evalVal :: Tm Z -> Property
prop_evalVal e = case eval e of
    Left _  -> discard
    Right v -> counterexample ("term: " ++ pp e) $
               counterexample ("value: " ++ pp v) $
               isVal v

-- | Evaluating a value is idempotent
prop_evalValIdem e = isVal e ==> case eval e of
    Left _  -> counterexample ("term: " ++ pp e) $
               property False
    Right v -> counterexample ("term: " ++ pp e) $
               counterexample ("value: " ++ pp v) $
               e == v


-- | The step function respects evaluation
prop_evalStep :: Tm Z -> Property
prop_evalStep e =
    case step e of
        Left _   -> discard
        Right e' -> counterexample ("e  = " ++ pp e) $
                    counterexample ("e' = " ++ pp e') $
                    eval e == eval e'

-- | Run quickcheck 1000 times
qc :: Testable prop => prop -> IO ()
qc = quickCheckWith stdArgs { maxSuccess = 1000 }
