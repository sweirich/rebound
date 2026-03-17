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
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tutorial"
    [ testGroup "ScopeCheck"
        [ QC.testProperty "project round-trip"  SC.prop_project_round_trip
        , QC.testProperty "parse round-trip"    SC.prop_parse_round_trip
        ]
    , testGroup "Eval"
        [ QC.testProperty "genVal produces values"        (TE.prop_genVal @Z)
        , QC.testProperty "val closed under subst"        (TE.prop_val_closed @Z)
        , QC.testProperty "eval produces a value"         TE.prop_evalVal
        , QC.testProperty "eval is idempotent on values"  TE.prop_evalValIdem
        , QC.testProperty "reduce produces inert terms"   (TE.prop_reduce_inert @Z)
        , QC.testProperty "step produces a value"         TE.prop_stepVal
        , QC.testProperty "step respects eval"            TE.prop_evalStep
        ]
    , testGroup "CPS"
        [ 
        QC.testProperty "cps result firstorder"         CPS.prop_cps_result_firstorder
        , QC.testProperty "cps eval simulates open"     CPS.prop_cps_eval_simulates_open
        , QC.testProperty "cpsOpt preserves step*"      CPS.prop_cpsOpt_steps
        , QC.testProperty "cpsOpt result firstorder"    CPS.prop_cpsOpt_result_firstorder
        , QC.testProperty "cpsOpt eval simulates open"  CPS.prop_cpsOpt_eval_simulates_open
        ]
    , testGroup "Exercise1"
        [ QC.testProperty "weaken"             Ex1.prop_weaken
        , QC.testProperty "ren/shift"          Ex1.prop_renShift
        , QC.testProperty "idE closed"         Ex1.prop_idE
        , QC.testProperty "idE open"           Ex1.prop_idE_open
        , QC.testProperty "compE"              Ex1.prop_compE
        , QC.testProperty "instantiate/weaken" Ex1.prop_instantiate_weaken
        ]
    , testGroup "Exercise3"
        [ -- QC.testProperty "colon reduces to cps"        Ex3.prop_a
          QC.testProperty "plotkin cps step*"           Ex3.prop_plotkin
        --, QC.testProperty "colon step simulation"       Ex3.prop_simulation
        ]
    ]
