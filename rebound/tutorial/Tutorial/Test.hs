
module Tutorial.Test where

import Test.Tasty
import Test.Tasty.QuickCheck qualified as QC

import Tutorial.Scoped.ScopeCheck qualified as SC
import Tutorial.Scoped.TestEval    qualified as TE
import Tutorial.Scoped.CPS         qualified as CPS

main :: IO ()
main = defaultMain all

all :: TestTree
all = testGroup "Tutorial"
    [ testGroup "ScopeCheck"
        [ QC.testProperty "project round-trip"  SC.prop_project_round_trip
        , QC.testProperty "parse round-trip"    SC.prop_parse_round_trip
        ]
    , testGroup "Eval"
        [ QC.testProperty "eval produces a value"    TE.prop_evalVal
        , QC.testProperty "eval is idempotent on values" TE.prop_evalValIdem
        , QC.testProperty "step respects eval"       TE.prop_evalStep
        ]
    , testGroup "CPS"
        [ QC.testProperty "cps preserves eval"  CPS.prop_cps_eval
        ]
    ]
