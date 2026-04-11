module Main where

import Test.Tasty
import Test.Tasty.QuickCheck qualified as QC

import Tutorial.Scoped.Syntax     (Nat(Z, S))
import Tutorial.Scoped.ScopeCheck qualified as SC
import Tutorial.Scoped.Gen        qualified as Gen
import Tutorial.Scoped.Eval       qualified as Eval
import Tutorial.Scoped.CPS        qualified as CPS
import Tutorial.Exercise1         qualified as Ex1
import Tutorial.Exercise2         qualified as Ex2
import Tutorial.Exercise3         qualified as Ex3

main :: IO ()
main = do
    putStrLn "=== ScopeCheck unit tests ==="
    SC.runUnitTests
    putStrLn "=== Eval ==="
    Eval.testAll
    putStrLn "=== CPS ==="
    CPS.testAll
    defaultMain allTests

allTests :: TestTree
allTests = testGroup "All"
    [ scopeCheckTests
    , exerciseTests
    ]

scopeCheckTests :: TestTree
scopeCheckTests = testGroup "ScopeCheck"
    [ QC.testProperty "project round-trip"
        (Gen.forAll0 Gen.Scoped Gen.Full SC.prop_project_round_trip)
    , QC.testProperty "parse round-trip"
        (Gen.forAll0 Gen.Scoped Gen.Full SC.prop_parse_round_trip)
    ]

exerciseTests :: TestTree
exerciseTests = testGroup "Exercises"
    [
      testGroup "Exercise2"
        [ QC.testProperty "idE closed"                  Ex3.prop_idE
        , QC.testProperty "idE open"                    Ex3.prop_idE_open
        , QC.testProperty "compE"                       Ex3.prop_compE
        , QC.testProperty "instantiate/weaken"          Ex3.prop_instantiate_weaken
        ]

    ]
