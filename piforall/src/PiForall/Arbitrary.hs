-- | This module is for testing the parser/pretty printer.
-- We would like to satisfy the following roundtrip property:
--     * if we generate a random AST term and print it, then it should parse back to an alpha-equivalent term
module PiForall.Arbitrary where

import Data.LocalName
import Data.Set qualified as Set
import Data.Vec qualified as Vec
import PiForall.ConcreteSyntax
import PiForall.PrettyPrint
import Test.QuickCheck
  ( Arbitrary (arbitrary),
    Gen,
    elements,
    frequency,
    sized,
  )
import Test.QuickCheck qualified as QC

-- View random terms
-- sampleTerms :: IO ()
-- sampleTerms = QC.sample' (arbitrary :: Gen Term) >>=
--    mapM_ (putStrLn . show)

---------------------------------------------------------------------------------------------------
-- Generators for the pi-forall expression AST
-- These generation functions and Arbitrary instances are tailored for testing the pretty printer
-- and parser. As a result, they do not generate "unprintable" parts of the AST, such as type annotations
-- and source code positions.

-- * Names

-- | variable names
-- drawn from a small list
genName :: Gen LocalName
genName = LocalName <$> elements ["x", "y", "z", "x0", "y0"]

instance Arbitrary LocalName where
  arbitrary = genName

tcNames :: [TyConName]
tcNames = ["T", "List", "Vec"]

dcNames :: [DataConName]
dcNames = ["K", "Nil", "Cons"]

arbConstructorNames :: ConstructorNames
arbConstructorNames = ConstructorNames (Set.fromList tcNames) (Set.fromList dcNames)

genTCName :: Gen TyConName
genTCName = elements tcNames

genDCName :: Gen DataConName
genDCName = elements dcNames

{- STUBWITH -}

-- * Core language

-- Terms with no subterms
base :: Gen Term
base =
  elements
    [ TyType {- TrustMe, PrintMe, -},
      tyUnit,
      litUnit,
      tyBool,
      litTrue,
      litFalse {-, Refl -}
    ]
  where
    tyUnit = {- SOLN DATA -} TyCon "Unit" [] {- STUBWITH TyUnit -}
    litUnit = {- SOLN DATA -} DataCon "()" [] {- STUBWITH LitUnit -}
    tyBool = {- SOLN DATA -} TyCon "Bool" [] {- STUBWITH TyBool -}
    litTrue = {- SOLN DATA -} DataCon "True" [] {- STUBWITH LitBool True -}
    litFalse = {- SOLN DATA -} DataCon "False" [] {- STUBWITH LitBool False -}

-- Generate a random term
-- In the inner recursion, the bool prevents the generation of TyCon/DataCon applications
-- inside Apps --- we want these terms to be fully saturated.
genTerm :: Int -> Gen Term
genTerm n
  | n <= 1 = base
  | otherwise = go True n
  where
    go b n0 =
      let n' = n0 `div` 2
       in frequency
            [ (1, Var <$> genName),
              (1, genLam n'),
              (1, App <$> go False n' <*> genTerm n'),
              (1, genPi n'),
              (1, genLet n'),
              {-
              (1, TyEq <$> go True n' <*> go True n'),
              (1, Subst <$> go True n' <*> go True n'),
              (1, Contra <$> go True n'),
               -}
              (if b then 1 else 0, TyCon <$> genTCName <*> genTerms n'),
              (if b then 1 else 0, DataCon <$> genDCName <*> genTerms n'),
              (1, Case <$> go True n' <*> genBoundedList 2 (genMatch n')),
              {- STUBWITH (1, If <$> genTerm n' <*> genTerm n' <*> genTerm n'),
              (1, genSigma n'),
              (1, Prod <$> genTerm n' <*> genTerm n'),
              (1, genLetPair n'), -}
              (1, base)
            ]

genTerms :: Int -> Gen [Term]
genTerms n = genBoundedList 2 (genTerm n)

genLam :: Int -> Gen Term
genLam n = do
  p <- genName
  b <- genTerm n
  return $ Lam p b

genPi :: Int -> Gen Term
genPi n = do
  p <- genName
  tyA <- genTerm n
  tyB <- genTerm n
  return $ Pi tyA p tyB

genLet :: Int -> Gen Term
genLet n = do
  p <- genName
  rhs <- genTerm n
  b <- genTerm n
  return $ Let p rhs b

genPattern :: Int -> Gen Pattern
genPattern n
  | n == 0 = PatVar <$> genName
  | otherwise =
      frequency
        [ (1, PatVar <$> genName),
          (1, PatCon <$> genDCName <*> genPatArgs)
        ]
  where
    n' = n `div` 2
    genPatArgs = genBoundedList 2 (genPattern n')

genMatch :: Int -> Gen Match
genMatch n = Branch <$> genPattern n <*> genTerm n

instance Arbitrary Pattern where
  arbitrary = sized genPattern
  shrink (PatCon n pats) = pats ++ [PatCon n pats' | pats' <- QC.shrink pats]
  shrink _ = []

instance Arbitrary Match where
  arbitrary = sized genMatch
  shrink (Branch pat bnd) = []

{- STUBWITH -}

instance Arbitrary Term where
  arbitrary = sized genTerm

  -- when QC finds a counterexample, it tries to shrink it to find a smaller one
  shrink (App tm arg) =
    [tm, arg]
      ++ [App tm' arg | tm' <- QC.shrink tm]
      ++ [App tm arg' | arg' <- QC.shrink arg]
  shrink (Lam _ bnd) = []
  shrink (Pi tyA _ bnd) = [tyA]
  shrink (Let _ rhs bnd) = [rhs]
  {-
      shrink (TyEq a b) = [a,b] ++ [TyEq a' b | a' <- QC.shrink a] ++ [TyEq a b' | b' <- QC.shrink b]
      shrink (Subst a b) = [a,b] ++ [Subst a' b | a' <- QC.shrink a] ++ [Subst a b' | b' <- QC.shrink b]
      shrink (Contra a) = a : [Contra a' | a' <- QC.shrink a]
  -}

  shrink (TyCon n as) = as ++ [TyCon n as' | as' <- QC.shrink as]
  shrink (DataCon n as) = as ++ [DataCon n as' | as' <- QC.shrink as]
  shrink (Case a ms) = [a] ++ [Case a' ms | a' <- QC.shrink a] ++ [Case a ms' | ms' <- QC.shrink ms]
  shrink _ = []

-------------------------------------------------------

-- * General quickcheck utilities

-- | Only generate lists up to size n
genBoundedList :: Int -> Gen a -> Gen [a]
genBoundedList b g = do
  len <- QC.elements [0 .. b]
  take len <$> QC.infiniteListOf g

-- | Run quickcheck for more than 100 tests
quickCheckN :: (QC.Testable prop) => Int -> prop -> IO ()
quickCheckN n = QC.quickCheckWith $ QC.stdArgs {QC.maxSuccess = n, QC.maxSize = 100}