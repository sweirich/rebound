module Examples.PTS where

import Data.Fin (f0, f1)
import PTS
import Rebound (Nat (S), appearsFree, idE, s1, snat, strengthenRec, zeroE)
import Rebound.Bind.PatN
import Test.Tasty
import Test.Tasty.HUnit
import Prelude hiding (pi)

lam :: Exp n -> Exp (S n) -> Exp n
lam tTy t = Lam tTy (bind1 t)

pi :: Exp n -> Exp (S n) -> Exp n
pi tTy t = Pi tTy (bind1 t)

instance Eq Err where _ == _ = False

all :: TestTree
all =
  testGroup
    "PTS"
    [ testCase "Is f0 free in t00?" $ appearsFree f0 t00 @?= True,
      testCase "Is f1 free in t00?" $ appearsFree f1 t00 @?= False,
      testCase "Weaken t00 by 1" $ weaken' s1 t00 @?= App (Var f0) (Var f0),
      testCase "Strengthen t00 by 1/1" $
        strengthenRec s1 s1 snat t00 @?= Just (App (Var f0) (Var f0)),
      testCase "Strengthen t01 by 1/1" $ strengthenRec s1 s1 snat t01 @?= Nothing,
      testCase "Pretty-print t0" $ show t0 @?= "λ *. 0",
      testCase "Pretty-print t1" $ show t1 @?= "λ *. λ *. 1 ((λ *. 0) 0)",
      testCase "Pretty-print tyid" $ show tyid @?= "Pi *. 0 -> 1",
      testCase "Pretty-print tmid" $ show tmid @?= "λ *. λ 0. 0",
      testCase "Eval t1" $
        eval t1 @?= lam Star (lam Star (Var f1 `App` (lam Star (Var f0) `App` Var f0))),
      testCase "Eval application" $
        eval (t1 `App` t0)
          @?= lam Star (lam Star (Var f0) `App` (lam Star (Var f0) `App` Var f0)),
      testCase "Step application" $
        step (t1 `App` t0)
          @?= Just (lam Star (lam Star (Var f0) `App` (lam Star (Var f0) `App` Var f0))),
      testCase "Normalize t1" $ nf t1 @?= lam Star (lam Star (Var f1 `App` Var f0)),
      testCase "Normalize application" $
        nf (t1 `App` t0) @?= lam Star (Var f0),
      testCase "EvalEnv t1" $
        evalEnv idE t1 @?= lam Star (lam Star (Var f1 `App` (lam Star (Var f0) `App` Var f0))),
      testCase "Type tmid" $ inferType zeroE tmid @?= Right (pi Star $ pi (Var f0) (Var f1)),
      testCase "Type application" $
        inferType zeroE (tmid `App` tyid)
          @?= Right (pi (pi Star (pi (Var f0) (Var f1))) (pi Star (pi (Var f0) (Var f1))))
    ]