{-|
Module      : Scoped.ScopeCheck
Description : Conversion between the scoped (de Bruijn) and named representations

This module provides two pairs of conversion functions:

* 'injectTy' / 'projectTy' — convert between the simple binary type language
  (@S.Ty@) and the n-ary named type language (@N.Ty@).

* 'injectTm' / 'projectTm' — convert between well-scoped de Bruijn terms
  (@S.Tm n@) and unscoped named terms (@N.Tm@).

The named representation is used for parsing and pretty-printing; the scoped
representation is used for evaluation and transformation.  The two directions
serve different purposes:

* __project__ (named → scoped): can fail; used after parsing.
* __inject__ (scoped → named): always succeeds; used for pretty-printing.

-}
module Tutorial.Scoped.ScopeCheck (
  -- * Scope-check errors
  ScopeCheckError(..),
  -- * Type conversions
  injectTy,
  projectTy,
  -- * Term conversions
  injectTmWith,
  injectTm,
  projectTmWith,
  projectTm,
  -- * Round-trip properties
  prop_project_round_trip,
  prop_parse_round_trip,
  testAll,
  -- * QuickCheck helpers
  forAll0,
  forAll1,
  forAll2,
  -- * pretty printer for scoped representation
  pp,
  ppWith,
  -- * parser for scoped representation
  Error(..),
  parse,
  parseWith
) where

import Test.QuickCheck

import Data.Fin
import Data.SNat
import Data.Vec (Vec(..), (!))
import qualified Rebound as Rebound

import qualified Tutorial.Named.Syntax as N
import qualified Tutorial.Named.PP as N
import qualified Tutorial.Named.Parser as N
import qualified Tutorial.Scoped.Syntax as S
import Tutorial.Scoped.Gen 
import Text.Parsec ( ParseError )

------------------------------------------------------------------------
-- * Parsing and Pretty Printing examples
------------------------------------------------------------------------

-- >>> N.parseTm "λ x y. x"
-- Right (Lam "x" (Lam "y" (Var "x")))

-- >>> projectTm (N.Lam "x" (N.Lam "y" (N.Var "x")))
-- Right (Lam (bind1 (Lam (bind1 (Var 1)))))

-- >>> parse "λ x y. x"
-- Right (Lam (bind1 (Lam (bind1 (Var 1)))))

-- Things can go wrong. 

-- >>> parse "λ x x"
-- Left (ParseError "<interactive>" (line 1, column 6):
-- unexpected end of input
-- expecting identifier or ".")

-- >>> parse "λ y . x"
-- Left (ScopeError (UnboundVariable "x"))


t1 :: S.Tm Z
t1 = case parse "λ x. x" of Right y -> y ; _ -> error "OOPS"
t2 :: S.Tm Z
t2 = case parse "λ y. y" of Right y -> y ; _ -> error "OOPS"

-- >>> t1 == t2
-- True


t3 :: S.Tm Z
t3 = case parse "λ x. λ y. x" of Right y -> y ; _ -> error "OOPS"
t4 :: S.Tm Z
t4 = case parse "λ x. λ y. y" of Right y -> y ; _ -> error "OOPS"

-- >>> t3 == t4
-- False

-- Pretty printing also goes through the named syntax

n1 :: N.Tm
n1 = injectTm t1
n2 :: N.Tm
n2 = injectTm t2

-- >>> n1
-- Lam "x" (Var "x")

-- >>> N.pp n1
-- "\\ x. x"


-- >>> pp t1
-- "\\ x. x"


-- we keep the original names

-- >>> n2
-- Lam "y" (Var "y")

-- >>> pp t3
-- "\\ x y. x"

t5 :: S.Tm Z
t5 = case parse "λ x. λ x. x" of Right y -> y ; _ -> error "OOPS"

-- >>> t5
-- Lam (bind1 (Lam (bind1 (Var 0))))

-- >>> pp t5
-- "\\ x x0. x0"


-- Can also parse and print open terms by providing additional information

-- >>> :t parseWith
-- parseWith :: [(String, Fin n)] -> String -> Either Error (Tm n)


-- >>> parseWith [("x", FZ)] "λ y. x"
-- Right (Lam (bind1 (Var 1)))


-- >>> :t ppWith
-- ppWith :: Vec n String -> Tm n -> String

-- >>> ppWith ("x" ::: VNil) (S.Lam (S.bind1 (S.LocalName "y") (S.Var f1)))
-- "\\ y. x"

------------------------------------------------------------------------
-- * Parsing and Pretty Printing (top-level entry points)
------------------------------------------------------------------------

-- | Errors that can occur during scope-checking.
data ScopeCheckError
  = UnboundVariable String
    -- ^ A variable name was not found in the current scope.
  | UnsupportedInjection Int
    -- ^ An injection index other than 0 or 1 was encountered.
  | UnsupportedForm N.Tm
    -- ^ The term uses a syntactic form that has no scoped equivalent,
    --   e.g. a tuple of arity other than 0 or 2, or an unrecognised
    --   pattern in a case expression.
  deriving (Show, Eq)

-- | Top-level errors from 'parse' / 'parseWith'.
data Error = ScopeError ScopeCheckError | ParseError ParseError
  deriving (Show)

-- | Parse a closed term
parse :: String -> Either Error (S.Tm Z)
parse s = case N.parseTm s of
              Left pe  -> Left (ParseError pe)
              Right ne -> case projectTm ne of
                            Left err -> Left (ScopeError err)
                            Right se -> Right se

-- >>> parse "\\ x y. x"
-- Right (Lam (bind1 (Lam (bind1 (Var 1)))))

-- >>> parse "λ y . x"
-- Left (ScopeError (UnboundVariable "x"))

-- | Parse an open term
parseWith :: [(String, Fin n)] -> String -> Either Error (S.Tm n)
parseWith vs s = case N.parseTm s of
              Left pe  -> Left (ParseError pe)
              Right ne -> case projectTmWith vs ne of
                            Left err -> Left (ScopeError err)
                            Right se -> Right se

-- | Pretty-print a closed term via the Named pretty printer
pp :: S.Tm Z -> String
pp = N.pp . injectTm

-- | Pretty-print an open term: requires names for the free variables
ppWith :: Vec n String -> S.Tm n -> String
ppWith e t = N.pp (injectTmWith e t)

------------------------------------------------------------------------
-- * Type conversions
------------------------------------------------------------------------

-- | Embed a simple binary type into the n-ary named type language.
-- Products become singleton @Prod@ lists and sums become singleton @Sum@ lists.
injectTy :: S.Ty -> N.Ty
injectTy = to where
    to (t1 S.:-> t2) = to t1 N.:-> to t2
    to S.One = N.unitTy
    to (t1 S.:* t2) = N.Prod [to t1, to t2]
    to (t1 S.:+ t2) = N.Sum [to t1, to t2]

-- | Project a named type back to a simple binary type.
-- Fails (@Nothing@) when the named type uses n-ary products or sums with
-- any arity other than 0 (unit) or 2 (binary product/sum).
projectTy :: N.Ty -> Maybe S.Ty
projectTy = to where
   to (t1 N.:-> t2) = (S.:->) <$> to t1 <*> to t2
   to (N.Prod []) = pure S.One
   to (N.Prod [t1,t2]) = (S.:*) <$> to t1 <*> to t2
   to (N.Prod _) = Nothing
   to (N.Sum [t1,t2]) = (S.:+) <$> to t1 <*> to t2
   to (N.Sum _) = Nothing

------------------------------------------------------------------------
-- * Term conversions
------------------------------------------------------------------------

-- | Test whether a name is already in a naming vector.
-- >>> inVec "x" ("x" ::: VNil)
-- True
inVec :: String -> Vec n String -> Bool
inVec _ VNil       = False
inVec x (y ::: ys) = x == y || inVec x ys

-- | Return @s@ if it does not appear in the vector, otherwise try
-- @s0@, @s1@, @s2@, … until a fresh name is found.
-- >>> freshen "x" ("x" ::: VNil)
-- "x0"
-- >>> freshen "x" (show (S.LocalName "x") ::: VNil)
-- "x0"
freshen :: String -> Vec n String -> String
freshen s vs
    | not (inVec s vs) = s
    | otherwise        = head [ s ++ show i | i <- [0 :: Int ..], not (inVec (s ++ show i) vs) ]

-- | Convert an open well-scoped term to a named term, given a vector of
-- names for the free variables.  The head of the vector (@index 'FZ'@) names
-- the innermost variable; names are prepended at each binder site.
injectTmWith :: Vec n String -> S.Tm n -> N.Tm
injectTmWith vs (S.Var x)     = N.Var (vs ! x)
injectTmWith vs (S.Lam t)     = N.Lam s (injectTmWith (s ::: vs) (S.getBody1 t))
                                  where s = freshen (show (S.getLocalName t)) vs
injectTmWith vs (S.App e1 e2) = N.App (injectTmWith vs e1) (injectTmWith vs e2)
injectTmWith vs (S.Unit)      = N.Pair []
injectTmWith vs (S.Pair e1 e2)= N.Pair [injectTmWith vs e1, injectTmWith vs e2]
injectTmWith vs (S.Inj i e)   = N.Inj i (injectTmWith vs e)
-- MatchUnit: the body has no new binders
injectTmWith vs (S.MatchUnit e1 e2) =
    N.Case (injectTmWith vs e1) [(N.unitTm, injectTmWith vs e2)]
-- MatchPair: two new variables are introduced; extend the context twice
injectTmWith vs (S.MatchPair e1 e2) =
    N.Case (injectTmWith vs e1) [(N.Pair [N.Var s1, N.Var s2], injectTmWith vs' e2')]
    where s1    = freshen (show (names ! FZ)) vs
          s2    = freshen (show (names ! FS FZ)) (s1 ::: vs)
          names = S.getLocalName2 e2
          e2'   = S.getBody2 e2
          vs'   = s2 ::: s1 ::: vs
-- MatchSum: each branch introduces one new variable
injectTmWith vs (S.MatchSum e e1 e2) =
    N.Case (injectTmWith vs e)
        [ (N.Inj 0 (N.Var s1), injectTmWith (s1 ::: vs) (S.getBody1 e1))
        , (N.Inj 1 (N.Var s2), injectTmWith (s2 ::: vs) (S.getBody1 e2)) ]
    where s1 = freshen (show (S.getLocalName e1)) vs
          s2 = freshen (show (S.getLocalName e2)) vs

-- | Convert a closed well-scoped term to a named term.
-- Variable names are taken from the 'S.LocalName' hints stored in binders.
injectTm :: S.Tm Z -> N.Tm
injectTm = injectTmWith VNil

-- | Convert a named term to a well-scoped term in scope @n@, given an
-- association list mapping in-scope variable names to their de Bruijn
-- indices.  Each binder prepends a new entry and shifts all existing
-- indices up by one.  Returns @Left err@ if a free variable is
-- encountered or if the term uses a syntactic form not supported by the
-- simple language (e.g. n-ary patterns).
projectTmWith :: [(String, Fin n)] -> N.Tm -> Either ScopeCheckError (S.Tm n)
-- A variable must be in scope; fail with UnboundVariable if not found
projectTmWith vs (N.Var v) = case lookup v vs of
    Nothing -> Left (UnboundVariable v)
    Just x  -> Right (S.Var x)
-- λ-abstraction: extend the scope with the bound name
projectTmWith vs (N.Lam v b) = do
    b' <- projectTmWith ((v, FZ) : map (fmap FS) vs) b
    return $ S.Lam (S.bind1 (S.LocalName v) b')
projectTmWith vs (N.App f a) = do
    f' <- projectTmWith vs f
    a' <- projectTmWith vs a
    return $ S.App f' a'
-- Empty tuple () maps to Unit
projectTmWith vs (N.Pair []) = return $ S.Unit
-- Binary tuple maps to Pair
projectTmWith vs (N.Pair [e1,e2]) = S.Pair <$> projectTmWith vs e1 <*> projectTmWith vs e2
-- Only injections 0 and 1 are supported
projectTmWith vs (N.Inj i e1)
    | i == 0 || i == 1 = S.Inj i <$> projectTmWith vs e1
    | otherwise        = Left (UnsupportedInjection i)
-- case e of { () -> e' }  maps to MatchUnit
projectTmWith vs (N.Case e [(N.Pair [], e1)]) =
    S.MatchUnit <$> projectTmWith vs e <*> projectTmWith vs e1
-- case e of { (v1, v2) -> e' }  maps to MatchPair
-- v2 is innermost (FZ), v1 is next (FS FZ)
projectTmWith vs (N.Case e [(N.Pair [N.Var v1, N.Var v2], e1)]) = do
    a' <- projectTmWith vs e
    b' <- projectTmWith ((v2, FZ) : (v1, FS FZ) : map (fmap (FS . FS)) vs) e1
    return (S.MatchPair a' (S.bind2 (S.LocalName v1) (S.LocalName v2) b'))
-- case e of { Inj0 v1 -> e1 ; Inj1 v2 -> e2 }  maps to MatchSum
projectTmWith vs (N.Case e [(N.Inj 0 (N.Var v1), e1), (N.Inj 1 (N.Var v2), e2)]) = do
    a'  <- projectTmWith vs e
    b1' <- projectTmWith ((v1, FZ) : map (fmap FS) vs) e1
    b2' <- projectTmWith ((v2, FZ) : map (fmap FS) vs) e2
    return (S.MatchSum a' (S.bind1 (S.LocalName v1) b1')
                          (S.bind1 (S.LocalName v2) b2'))
-- Any other form is not supported
projectTmWith vs t = Left (UnsupportedForm t)

-- | Convert a named term to a closed well-scoped term.
-- Returns @Left err@ if the named term contains free variables or uses
-- syntactic forms not supported by the simple language (e.g. n-ary patterns).
projectTm :: N.Tm -> Either ScopeCheckError (S.Tm Z)
projectTm = projectTmWith []

------------------------------------------------------------------------
-- * Round-trip properties
------------------------------------------------------------------------

-- | Injecting a scoped term into named form and projecting back yields
-- the original term.
prop_project_round_trip :: S.Tm Z -> Bool
prop_project_round_trip i = projectTm ((injectTm i) :: N.Tm) == Right i

-- | Pretty-printing a term and parsing it back yields the original named term.
prop_parse_round_trip :: S.Tm Z -> Bool
prop_parse_round_trip i = N.parseTm (show (N.test (injectTm i :: N.Tm))) == Right (injectTm i)

------------------------------------------------------------------------
-- * Utilities for testing
------------------------------------------------------------------------

-- | Test a property on a closed term 
forAll0 :: Testable a => Constraint -> Language -> (S.Tm Z -> a) -> Property
forAll0 c l = forAllShrinkShow (genTm c l) (shrinkTm c) pp

-- | Test a property on a term with a single free variable "x" 
forAll1 :: Testable a => Constraint -> Language -> (S.Tm (S Z) -> a) -> Property
forAll1 c l = forAllShrinkShow (genTm c l) (shrinkTm c) (ppWith ("x" ::: VNil))

-- | Test a property on a term with two free variables "x" and "y"
forAll2 :: Testable a => Constraint -> Language -> (S.Tm (S (S Z)) -> a) -> Property
forAll2 c l = forAllShrinkShow (genTm c l) (shrinkTm c) (ppWith ("x" ::: "y" ::: VNil))

-- | Run all QuickCheck properties in this module.
testAll :: IO ()
testAll = do
    let args = stdArgs { maxSuccess = 1000 }
    putStrLn "prop_project_round_trip:" 
    quickCheckWith args (forAll0 Scoped Full prop_project_round_trip)
    putStrLn "prop_parse_round_trip:"   
    quickCheckWith args (forAll0 Scoped Full prop_parse_round_trip)
