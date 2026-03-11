module Tutorial.Scoped.Eval.Test where

import Test.QuickCheck

import Tutorial.Scoped.Syntax
import Tutorial.Scoped.Eval
import Tutorial.Scoped.Gen
import Tutorial.Scoped.ScopeCheck

-- | The result of evaluation is a value
prop_evalVal :: Tm Z -> Property
prop_evalVal e = case eval e of
    Nothing -> discard
    Just v  -> counterexample ("term: " ++ pp e) $
               counterexample ("value: " ++ pp v) $
               isVal v

-- | Evaluating a value is idempotent
prop_evalValIdem e = isVal e ==> case eval e of
    Nothing -> counterexample ("term: " ++ pp e) $
               property False
    Just v -> counterexample ("term: " ++ pp e) $
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
