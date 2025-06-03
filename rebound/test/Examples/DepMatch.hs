module Examples.DepMatch where

import Data.Fin (f0, f1)
import DepMatch
import Rebound (N2, Nat (S), appearsFree, s1, snat, strengthenRec, zeroE, (.:))
import Rebound.Bind.PatN (bind1)
import Test.Tasty
import Test.Tasty.HUnit
import Utils

instance Eq Err where _ == _ = False

sig :: Exp n -> Exp (S n) -> Exp n
sig l r = Sigma l (bind1 r)

all :: TestTree
all =
  testGroup
    "DepMatch"
    [ testCase "Pattern-match tm0 with pat0" $
        ((snat,) <$> patternMatch pat0 tm0) @?= Just (snat @N2, sig Star (Var f0) .: (Star .: zeroE)),
      testCase "Is f0 free in t00?" $ appearsFree f0 t00 @?= True,
      testCase "Is f1 free in t00?" $ appearsFree f1 t00 @?= False,
      testCase "Weaken t00 by 1" $ weaken' s1 t00 @?= (Var f0 `App` Var f0),
      testCase "Strengthen t00 by 1/1" $ strengthenRec s1 s1 snat t00 @?= Just (Var f0 `App` Var f0),
      testCase "Strengthen t01 by 1/1" $ strengthenRec s1 s1 snat t01 @?= Nothing,
      testCase "Pretty-print t0" $ show t0 @?= "λ_. 0",
      testCase "Pretty-print t1" $ show t1 @?= "λ_. (λ_. (1 (λ_. (0 0))))",
      testCase "Pretty-print tyid" $ show tyid @?= "Pi *. 0 -> 1",
      testCase "Pretty-print tmid" $ show tmid @?= "λ_. (λ_. 0)",
      testCase "Eval t1" $ eval t1 @?= lam (lam $ Var f1 `App` lam (Var f0 `App` Var f0)),
      testCase "Eval application" $
        eval (t1 `App` t0) @?= lam (lam (Var f0) `App` lam (Var f0 `App` Var f0)),
      testCase "Step application" $
        step (t1 `App` t0) @?= Just (lam (lam (Var f0) `App` lam (Var f0 `App` Var f0))),
      testCase "Check tmid : tyid" $ checkType zeroE tmid tyid @?= Right (),
      testCase "Type (tmid tyid)" $ case inferType zeroE (tmid `App` tyid) of
        Left (AnnotationNeeded err) -> err @?= lam (lam (Var f0))
        _ -> assertFailure "Expected an `AnnotationNeeded` error."
    ]