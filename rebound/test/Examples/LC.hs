module Examples.LC where

import HOAS qualified
import LC
import LCQC qualified
import Rebound (zeroE)
import ScopeCheck qualified
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck qualified as QC

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
      testCase "WHNF" $ show (whnfEnv zeroE t) @?= "(λ. ((0 ((λ. 0) 0)) (λ. 0)))",
      localOption (QC.QuickCheckTests 10) $
        testGroup
          "LCQC"
          [ QC.testProperty "nf1 normalizes" LCQC.prop_nf1,
            QC.testProperty "nfEnv normalizes" LCQC.prop_nfEnv
          ],
      testGroup
        "ScopeCheck"
        [ testCase "Scope idExp" $ ScopeCheck.scopeCheck ScopeCheck.idExp @?= Just t0,
          testCase "Scope trueExp" $ ScopeCheck.scopeCheck ScopeCheck.trueExp @?= Just (lam $ lam v1),
          testCase "Scope ill-scoped" $ ScopeCheck.scopeCheck ScopeCheck.illScoped @?= Nothing
        ],
      testGroup
        "HOAS"
        [ testCase "Convert tru" $ HOAS.cvt HOAS.tru @?= lam (lam v1),
          testCase "Convert tru" $ HOAS.cvt HOAS.fls @?= lam (lam v0),
          testCase "Convert app" $ HOAS.cvt HOAS.app @?= lam (lam $ v1 @@ v0),
          testCase "Convert omega" $ HOAS.cvt HOAS.omega @?= (lam (v0 @@ v0) @@ lam (v0 @@ v0))
        ]
    ]