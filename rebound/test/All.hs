import Examples.DepMatch qualified as DepMatch
import Examples.LC qualified as LC
import Examples.LCLet qualified as LCLet
import Examples.PTS qualified as PTS
import Examples.Pat qualified as Pat
import Examples.SystemF qualified as SystemF
import Test.Tasty

main :: IO ()
main = do
  defaultMain $
    testGroup
      "All"
      [ LC.all,
        LCLet.all,
        Pat.all,
        SystemF.all,
        PTS.all,
        DepMatch.all
      ]