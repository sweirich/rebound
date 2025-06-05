module Examples.PureSystemF where

import Data.Fin (f0, f1)
import PureSystemF
import Rebound (LocalName (..))
import Rebound.Bind.Local (bind)
import Test.Tasty
import Test.Tasty.HUnit

pureTC t = runTC emptyEnv $ inferType t

bbNat = TAll $ bind (LocalName "X") $ TArr (TArr (Var f0) (Var f0)) (TArr (Var f0) (Var f0))

all :: TestTree
all =
  testGroup
    "SystemF"
    [ testGroup
        "Diadic"
        -- TODO: add test cases
        [],
      testGroup
        "Pure"
        [ testCase "Pretty-print t0" $ show t0 @?= "ΛX. λx. x",
          testCase "Pretty-print t1" $ show t1 @?= "ΛX. λf. λx. f [X] x",
          testCase "Pretty-print t2" $ show t2 @?= "λX. λx. x",
          testCase "Infer t0" $
            pureTC t0
              @?= Right (TAll $ bind (LocalName "X") (TArr (Var f0) (Var f0))),
          testCase "Infer t1" $
            pureTC t1
              @?= Right
                ( TAll $
                    bind
                      (LocalName "X")
                      ( TArr
                          (TAll $ bind (LocalName "Y") (TArr (Var f0) (Var f0)))
                          (TArr (Var f0) (Var f0))
                      )
                ),
          testCase "Infer t2" $ pureTC t2 @?= Left "Term variable occurs in type",
          testCase "Infer Boehm-Berarducci Nat 0" $ pureTC bbn0 @?= Right bbNat,
          testCase "Infer Boehm-Berarducci Nat 1" $ pureTC bbn1 @?= Right bbNat,
          testCase "Infer Boehm-Berarducci Nat 2" $ pureTC bbn2 @?= Right bbNat
        ]
    ]