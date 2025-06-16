module Examples.LinLC where

import Data.Vec qualified as Vec
import LinLC
import Rebound (Nat (Z))
import Test.Tasty
import Test.Tasty.HUnit

tcS :: Exp Z -> Ty -> Assertion
tcS t ty = runTC Vec.empty (checkType t ty) @?= Right ()

tcF :: Exp Z -> Ty -> String -> Assertion
tcF t ty msg = runTC Vec.empty (checkType t ty) @?= Left msg

all :: TestTree
all =
  testGroup
    "LinLC"
    [ testCase "Check id" $
        tcS (lam v0) (TyUnit ~> TyUnit),
      testCase "Check app" $
        tcS (lam $ lam $ v0 @@ v1) (TyUnit ~> (TyUnit ~> TyUnit) ~> TyUnit),
      testCase "Check 1 unused" $
        tcF
          (lam $ lam v1)
          (TyUnit ~> (TyUnit ~> TyUnit) ~> TyUnit)
          "Variable was not used.",
      testCase "Check type mismatch" $
        tcF
          (lam $ lam v0)
          (TyUnit ~> (TyUnit ~> TyUnit) ~> TyUnit)
          "Inferred type does not match expected type.",
      testCase "Check 2 unused" $
        tcF
          (lam $ lam v0)
          (TyUnit ~> (TyUnit ~> TyUnit) ~> TyUnit ~> TyUnit)
          "Variable was not used."
    ]