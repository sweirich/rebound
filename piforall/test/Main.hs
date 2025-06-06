{-# LANGUAGE LambdaCase #-}

module Main where

import Control.Monad.Except
import Data.List (intercalate)
import Data.Maybe (isJust)
import ParseResolveRT as UnRT
import ParseScopeRT as AutoPiForall
import PiForall.Rebound.Environment qualified as AutoPiForall
import PiForall.Rebound.Equal qualified as AutoPiForall
import PiForall.Rebound.Modules qualified as AutoPiForall
import PiForall.Rebound.Syntax qualified as AutoPiForall
import PiForall.Rebound.TypeCheck qualified as AutoPiForall
import PiForall.Unbound.Environment qualified as UnPiForall
import PiForall.Unbound.Equal qualified as UnPiForall
import PiForall.Unbound.Modules qualified as UnPiForall
import PiForall.Unbound.Syntax qualified as UnPiForall
import PiForall.Unbound.TypeCheck qualified as UnPiForall
import PiForall.Log qualified as Log
import PiForall.PrettyPrint as PP
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck qualified as QC
import Text.ParserCombinators.Parsec.Error

--------------------------------------------------------------------------------
-- Definition of tests to run
--------------------------------------------------------------------------------

positiveTests :: ([String] -> Bool -> String -> TestTree) -> String -> [String] -> [TestTree]
positiveTests tcFile path tests = tcFile [path] True <$> tests

negativeTests :: ([String] -> Bool -> String -> TestTree) -> String -> [String] -> [TestTree]
negativeTests tcFile path tests = tcFile [path] False <$> tests

std :: ([String] -> Bool -> String -> TestTree) -> TestTree
std tcFile =
  testGroup
    "Standard Library"
    ( positiveTests
        tcFile
        "pi/std"
        [ "Equality",
          "List",
          "Option",
          "Vec",
          "HList",
          "Logic"
        ]
    )

examples :: ([String] -> Bool -> String -> TestTree) -> TestTree
examples tcFile =
  testGroup
    "Examples"
    ( positiveTests
        tcFile
        "pi/examples"
        [ -- "Lennart",
          "Hurkens",
          "Lambda",
          "Lambda0",
          "Lambda1",
          "Lambda2",
          "Compiler",
          "Regex",
          "AVL",
          "AVL_F"
        ]
    )

baseTests :: ([String] -> Bool -> String -> TestTree) -> TestTree
baseTests tcFile = testGroup "Base tests" (negativeTests tcFile "test/base" ["Fail", "ConstructorEvidence"])

bugs :: ([String] -> Bool -> String -> TestTree) -> TestTree
bugs tcFile =
  testGroup
    "Bugs"
    ( positiveTests
        "test/reproducers"
        [ -- https://github.com/sweirich/Rebound/pull/2
          "Bug1",
          "Bug2"
        ]
    )
  where
    positiveTests :: String -> [String] -> [TestTree]
    positiveTests path tests = tcFile [path] True <$> tests

main :: IO ()
main = do
  defaultMain $
    testGroup
      "/"
      [ testGroup
          "Unbound"
          [ QC.testProperty "PP-Parsing round trip" UnRT.prop_roundtrip,
            std unTcFile,
            examples unTcFile
          ],
        testGroup
          "Rebound"
          [ QC.testProperty "PP-Parsing round trip" AutoPiForall.prop_roundtrip,
            std autoTcFile,
            examples autoTcFile,
            baseTests autoTcFile,
            bugs autoTcFile
          ]
      ]

--------------------------------------------------------------------------------
-- Helpers for tests definition
--------------------------------------------------------------------------------

standardLibrary :: [String]
standardLibrary = ["pi/std"]

--------------------------------------------------------------------------------
-- Testing functions
--------------------------------------------------------------------------------
autoTcFile :: [String] -> Bool -> String -> TestTree
autoTcFile path positive name =
  testCase (name ++ if positive then " [✔]" else " [✘]") $ do
    v <- runExceptT (AutoPiForall.getModules (path ++ standardLibrary) name)
    case v of
      Left err -> assertFailure $ "Parsing error:" ++ show err
      Right val -> case AutoPiForall.runTcMonad (AutoPiForall.tcModules val) of
        (Left err, _) -> assertFailure $ "Type error:\n" ++ show (AutoPiForall.displayErr err PP.initDI)
        (Right res, logs) -> case filter (not . Log.isInfo) logs of
          logs@(_:_) -> assertFailure $ "Warnings were produced:" ++ intercalate "\n" (fmap show logs)
          _ -> return ()

unTcFile :: [String] -> Bool -> String -> TestTree
unTcFile path positive name =
  testCase (name ++ if positive then " [✔]" else " [✘]") $ do
    v <- runExceptT (UnPiForall.getModules (path ++ standardLibrary) name)
    case v of
      Left err -> assertFailure $ "Parsing error:" ++ show err
      Right val -> case UnPiForall.runTcMonad UnPiForall.emptyEnv (UnPiForall.tcModules val) of
        (Left err, _) -> assertFailure $ "Type error:\n" ++ show (UnPiForall.dispErr err)
        (Right res, logs) -> case filter (not . Log.isInfo) logs of
          logs@(_:_) -> assertFailure $ "Warnings were produced:" ++ intercalate "\n" (fmap show logs)
          _ -> return ()
