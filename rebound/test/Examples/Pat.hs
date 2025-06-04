module Examples.Pat where

import Pat
import Rebound (N2, Nat (Z), snat, zeroE, (.:))
import Test.Tasty
import Test.Tasty.HUnit
import Utils

all :: TestTree
all =
  testGroup
    "Pat"
    [ testCase "Pretty-print t0" $ show t0 @?= "λ. 0",
      testCase "Pretty-print t1" $ show t1 @?= "λ. λ. 1 (λ. 0 0)",
      testCase "Pretty-print t2" $ show t2 @?= "λ. case 0 of [Nil => 0,(Cons V) V => 0]",
      testCase "Pretty-print t3" $ show t3 @?= "(cons a) ((cons b) nil)",
      testCase "Pretty-print t4" $ show t4 @?= "λ. case 0 of [Nil => 0,(Cons V) V => 0] ((cons a) ((cons b) nil))",
      testCase "Pattern-match e1 with p1" $
        ((snat @N2,) <$> patternMatch p1 e1) @?= Just (snat @N2, Con "B" .: (Con "A" .: zeroE @_ @Z)),
      testCase "Pattern-match e1 with p2" $ ((snat @N2,) <$> patternMatch p2 e1) @?= Nothing,
      testCase "Pattern-match e2 with p1" $ ((snat @N2,) <$> patternMatch p1 e2) @?= Nothing,
      testCase "Pattern-match e2 with p2" $
        ((snat @N2,) <$> patternMatch p2 e2) @?= Just (snat @N2, Con "C" .: (Con "A" .: zeroE @_ @Z)),
      testCase "Eval t1" $ show (eval t1) @?= "λ. λ. 1 (λ. 0 0)",
      testCase "Eval application" $ show (eval (t1 `App` t0)) @?= "λ. λ. 0 (λ. 0 0)",
      testCase "Eval t4" $ show (eval t4) @?= "case (cons a) ((cons b) nil) of [Nil => (cons a) ((cons b) nil),(Cons V) V => 0]",
      testCase "Step application" $ show (step (t1 `App` t0)) @?= "Just (λ. λ. 0 (λ. 0 0))",
      testCase "Normalize t1" $ show (nf t1) @?= "λ. λ. 1 0",
      testCase "Normalize application" $ show (nf (t1 `App` t0)) @?= "λ. λ. 0 0"
    ]