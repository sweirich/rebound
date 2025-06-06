import Examples.DepMatch qualified as DepMatch
import Examples.LC qualified as LC
import Examples.LCLet qualified as LCLet
import Examples.PTS qualified as PTS
import Examples.Pat qualified as Pat
import Examples.PureSystemF qualified as PureSystemF
import Test.Tasty

main :: IO ()
main = do
  defaultMain $
    testGroup
      "All"
      [ LC.all,
        LCLet.all,
        Pat.all,
        testGroup
          "System F"
          [ -- TODO: add System F tests
            PureSystemF.all
          ],
        PTS.all,
        DepMatch.all
      ]