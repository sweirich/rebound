module Main where

import Test.Tasty
import Test.Tasty.QuickCheck qualified as QC

import Tutorial.Scoped.Syntax     (Nat(Z, S))
import Tutorial.Scoped.ScopeCheck qualified as SC
import Tutorial.Scoped.Eval       qualified as TE
import Tutorial.Scoped.CPS        qualified as CPS
import Tutorial.Exercise1         qualified as Ex1
import Tutorial.Exercise2         qualified as Ex2
import Tutorial.Exercise3         qualified as Ex3

main :: IO ()
main = do
    putStrLn "=== ScopeCheck ==="
    SC.testAll
    putStrLn "=== Eval ==="
    TE.testAll
    putStrLn "=== CPS ==="
    CPS.testAll
    defaultMain exerciseTests

exerciseTests :: TestTree
exerciseTests = testGroup "Exercises"
    [ 
      testGroup "Exercise2"
        [ QC.testProperty "idE closed"                  Ex2.prop_idE
        , QC.testProperty "idE open"                    Ex2.prop_idE_open
        , QC.testProperty "compE"                       Ex2.prop_compE
        , QC.testProperty "instantiate/weaken"          Ex2.prop_instantiate_weaken
        , QC.testProperty "normalize/normal closed"     (Ex2.prop_normalize_normal  @Z)
        , QC.testProperty "normalize/normal open"       (Ex2.prop_normalize_normal  @(S Z))
        , QC.testProperty "normalize/idempotent closed" (Ex2.prop_normalize_idempotent @Z)
        , QC.testProperty "normalize/idempotent open"   (Ex2.prop_normalize_idempotent @(S Z))
        , QC.testProperty "normalize/eval"              Ex2.prop_normalize_eval
        , QC.testProperty "normalize/reduce closed"     (Ex2.prop_normalize_reduce  @Z)
        , QC.testProperty "normalize/reduce open"       (Ex2.prop_normalize_reduce  @(S Z))
        ]
    , testGroup "Exercise3"
        [ QC.testProperty "plotkin cps step*"  Ex3.prop_plotkin
        ]
    ]
