module Examples.LC where

import LC
import Rebound (zeroE)
import Test.Tasty
import Test.Tasty.HUnit

all :: TestTree
all =
  testGroup
    "LC"
    [ testCase "Pretty-print t0" $ show t0 @?= "(λ. 0)",
      testCase "Eval application" $ eval (t `App` t0) @?= t0,
      testCase "Pretty-print t2" $ show t2 @?= "((λ. (λ. 1)) ((λ. 0) (λ. 0)))",
      testCase "Eval t2" $ show (eval t2) @?= "(λ. (λ. 0))",
      testCase "Step application" $ step (t0 `App` t0) @?= Just t0,
      testCase "Eval' application" $ eval' 5 (t `App` t0) @?= Just t0,
      testCase "WHNF" $ show (whnfEnv zeroE t) @?= "(λ. ((0 ((λ. 0) 0)) (λ. 0)))"
    ]