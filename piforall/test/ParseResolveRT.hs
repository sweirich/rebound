module ParseResolveRT where

import Test.QuickCheck qualified as QC
import PiForall.Unbound.NameResolution
import PiForall.ConcreteSyntax
import PiForall.Parser (expr, testParser)

import Text.Parsec.Error (ParseError)
import PiForall.PrettyPrint
import PiForall.Arbitrary
import Unbound.Generics.LocallyNameless qualified as Unbound

-- | Round trip property: a given term prints then parses to the same term.
prop_roundtrip :: Term -> QC.Property
prop_roundtrip tm
  | Just stm <- resolveNames tm =
      let str = pp $ nominalize stm
       in case test_parseExpr str of
            Left err -> QC.counterexample ("*** Could not parse:\n" ++ str ++ "\n" ++ show err) False
            Right tm' ->
              case resolveNames tm' of
                Just stm' ->
                  QC.counterexample
                    ( "*** Round trip failure! Parsing:\n"
                        ++ str
                        ++ "\n** printed from \n"
                        ++ show stm
                        ++ "\n*** results in\n"
                        ++ show stm'
                        ++ "\n*** printed as\n"
                        ++ pp (nominalize  stm')
                    )
                    (stm `Unbound.aeq` stm')
                Nothing ->
                  QC.counterexample "*** Round trip failure! ScopeCheck result of parsing" False
  | otherwise = QC.property False

test_parseExpr :: String -> Either Text.Parsec.Error.ParseError Term
test_parseExpr = testParser arbConstructorNames expr