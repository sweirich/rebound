module Examples.LCLet where

import LCLet
import Test.Tasty
import Test.Tasty.HUnit

all :: TestTree
all =
  testGroup
    "LCLet"
    [ testCase "Pretty-print t0" $ show t0 @?= "(λ. 0)",
      testCase "Pretty-print t1" $ show t1 @?= "(λ. (λ. (1 ((λ. 0) 0))))",
      testCase "Pretty-print t2" $ show t2 @?= "(let (λ. 0) in (0 0))",
      testCase "Pretty-print t3" $ show t3 @?= "(let rec (λ. (0 (1 0))) in 0)",
      testCase "Pretty-print t4" $ show t4 @?= "<let-tele>",
      testCase "Eval t1" $ show (eval t1) @?= "(λ. (λ. (1 ((λ. 0) 0))))",
      testCase "Eval application" $ show (eval (t1 @@ t0)) @?= "(λ. ((λ. 0) ((λ. 0) 0)))",
      testCase "Eval t2" $ show (eval t2) @?= "(λ. 0)",
      -- testCase "Eval t3" $ show (eval t3) @?= <Infinite loop>,
      testCase "Eval t4" $ show (eval t4) @?= "(λ. 0)"
    ]