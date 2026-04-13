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
import Tutorial.Exercise4         qualified as Ex4

main :: IO ()
main = do
    putStrLn "=== ScopeCheck unit tests ==="
    SC.runUnitTests
    putStrLn "=== Eval ==="
    Eval.testAll
    putStrLn "=== CPS ==="
    CPS.testAll
    putStrLn "=== Exercise3 ==="
    Ex3.testAll
    putStrLn "=== Exercise4 ==="
    Ex4.testAll
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
      testGroup "Exercise3"
        [ QC.testProperty "idE closed"                  Ex3.prop_idE
        , QC.testProperty "idE open"                    Ex3.prop_idE_open
        , QC.testProperty "compE"                       Ex3.prop_compE
        , QC.testProperty "instantiate/weaken"          Ex3.prop_instantiate_weaken
        , QC.testProperty "project round-trip open"     (Gen.forAll1 Gen.Scoped Gen.Full Ex3.prop_project_round_trip_open)
        , QC.testProperty "stepVal"                     (Gen.forAll0 Gen.Typed Gen.Full Ex3.prop_stepVal)
        , QC.testProperty "evalStep"                    (Gen.forAll0 Gen.Typed Gen.Full Ex3.prop_evalStep)
        , QC.testProperty "reduceStep"                  (Gen.forAll1 Gen.Typed Gen.Full Ex3.prop_reduceStep)
        , QC.testProperty "normalize/normal"            (Gen.forAll0 Gen.Typed Gen.Full Ex3.prop_normalize_normal)
        , QC.testProperty "normalize/idempotent closed" (Gen.forAll0 Gen.Typed Gen.Full (Ex3.prop_normalize_idempotent @Z))
        , QC.testProperty "normalize/idempotent open"   (Gen.forAll1 Gen.Typed Gen.Full (Ex3.prop_normalize_idempotent @(S Z)))
        , QC.testProperty "normalize/eval"              (Gen.forAll0 Gen.Typed Gen.Full Ex3.prop_normalize_eval)
        ]

    , testGroup "Exercise4"
        [ 
          QC.testProperty "cpsOpt steps pure" Ex4.prop_cpsOpt_steps_pure
        ]
    ]
