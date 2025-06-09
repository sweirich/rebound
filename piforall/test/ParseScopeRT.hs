module ParseScopeRT where

import Test.QuickCheck qualified as QC
import PiForall.Rebound.ScopeCheck
import PiForall.ConcreteSyntax
import PiForall.Parser (expr, testParser)

import Text.Parsec.Error (ParseError)
import PiForall.PrettyPrint
import PiForall.Arbitrary

-- | Round trip property: a given term prints then parses to the same term.
prop_roundtrip :: Term -> QC.Property
prop_roundtrip tm
  | Just stm <- scope tm =
      let str = pp $ unscope stm
       in case test_parseExpr str of
            Left err -> QC.counterexample ("*** Could not parse:\n" ++ str ++ "\n" ++ show err) False
            Right tm' ->
              case scope tm' of
                Just stm' ->
                  QC.counterexample
                    ( "*** Round trip failure! Parsing:\n"
                        ++ str
                        ++ "\n** printed from \n"
                        ++ show stm
                        ++ "\n*** results in\n"
                        ++ show stm'
                        ++ "\n*** printed as\n"
                        ++ pp (unscope  stm')
                    )
                    (stm == stm')
                Nothing ->
                  QC.counterexample "*** Round trip failure! ScopeCheck result of parsing" False
  | otherwise = QC.property False

test_parseExpr :: String -> Either Text.Parsec.Error.ParseError Term
test_parseExpr = testParser arbConstructorNames expr