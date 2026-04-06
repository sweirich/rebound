module Main where

import Test.Tasty
import Test.Tasty.QuickCheck qualified as QC

import Tutorial.Scoped.Syntax     (Nat(Z))
import Tutorial.Scoped.ScopeCheck qualified as SC
import Tutorial.Scoped.Eval       qualified as TE
import Tutorial.Scoped.CPS        qualified as CPS
import Tutorial.Exercise1         qualified as Ex1
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
    [ testGroup "Exercise1"
        [ QC.testProperty "weaken"             Ex1.prop_weaken
        , QC.testProperty "ren/shift"          Ex1.prop_renShift
        , QC.testProperty "idE closed"         Ex1.prop_idE
        , QC.testProperty "idE open"           Ex1.prop_idE_open
        , QC.testProperty "compE"              Ex1.prop_compE
        , QC.testProperty "instantiate/weaken" Ex1.prop_instantiate_weaken
        ]
    , testGroup "Exercise3"
        [ QC.testProperty "plotkin cps step*"  Ex3.prop_plotkin
        ]
    ]
