{-|
Module      : Scoped.ScopeCheck
Description : Conversion between the scoped (de Bruijn) and named representations

This module provides two pairs of conversion functions:

* 'injectTy' / 'projectTy' — convert between the simple binary type language
  (@I.Ty@) and the n-ary named type language (@N.Ty@).

* 'injectTm' / 'projectTm' — convert between well-scoped de Bruijn terms
  (@I.Tm n@) and unscoped named terms (@N.Tm@).

The named representation is used for parsing and pretty-printing; the scoped
representation is used for evaluation and transformation.  The two directions
serve different purposes:

* __inject__ (scoped → named): always succeeds; used for display.
* __project__ (named → scoped): can fail; used after parsing.

-}
module Tutorial.Scoped.ScopeCheck (
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
  -- * pretty printer
  pp
) where

import Test.QuickCheck

import Data.Fin
import Data.SNat
import Data.Vec (Vec(..), (!))
import qualified Rebound as Rebound

import qualified Tutorial.Named.Syntax as N
import qualified Tutorial.Named.PP as N
import qualified Tutorial.Named.Parser as N
import qualified Tutorial.Scoped.Syntax as I
import Tutorial.Scoped.Gen


-- | Pretty-print a closed term via the Named pretty printer
pp :: I.Tm Z -> String
pp = N.pp . injectTm

------------------------------------------------------------------------
-- * Type conversions
------------------------------------------------------------------------

-- | Embed a simple binary type into the n-ary named type language.
-- Products become singleton @Prod@ lists and sums become singleton @Sum@ lists.
injectTy :: I.Ty -> N.Ty
injectTy = to where
    to (t1 I.:-> t2) = to t1 N.:-> to t2
    to I.One = N.unitTy
    to I.Zero = N.voidTy
    to (t1 I.:* t2) = N.Prod [to t1, to t2]
    to (t1 I.:+ t2) = N.Sum [to t1, to t2]

-- | Project a named type back to a simple binary type.
-- Fails (@Nothing@) when the named type uses n-ary products or sums with
-- any arity other than 0 (unit/void) or 2 (binary product/sum).
projectTy :: N.Ty -> Maybe I.Ty
projectTy = to where
   to (t1 N.:-> t2) = (I.:->) <$> to t1 <*> to t2
   to (N.Prod []) = pure I.One
   to (N.Prod [t1,t2]) = (I.:*) <$> to t1 <*> to t2
   to (N.Prod _) = Nothing
   to (N.Sum []) = pure I.Zero
   to (N.Sum [t1,t2]) = (I.:+) <$> to t1 <*> to t2
   to (N.Sum _) = Nothing

------------------------------------------------------------------------
-- * Term conversions
------------------------------------------------------------------------

-- | Test whether a name is already in a naming vector.
inVec :: String -> Vec n String -> Bool
inVec _ VNil       = False
inVec x (y ::: ys) = x == y || inVec x ys

-- | Return @s@ if it does not appear in the vector, otherwise try
-- @s0@, @s1@, @s2@, … until a fresh name is found.
freshen :: String -> Vec n String -> String
freshen s vs
    | not (inVec s vs) = s
    | otherwise        = head [ s ++ show i | i <- [0 :: Int ..], not (inVec (s ++ show i) vs) ]

-- | Convert an open well-scoped term to a named term, given a vector of
-- names for the free variables.  The head of the vector (@index 'FZ'@) names
-- the innermost variable; names are prepended at each binder site.
injectTmWith :: Vec n String -> I.Tm n -> N.Tm
injectTmWith vs (I.Var x)     = N.Var (vs ! x)
injectTmWith vs (I.Lam t)     = N.Lam s (injectTmWith (s ::: vs) (I.getBody1 t))
                                  where s = freshen (show (I.getLocalName t)) vs
injectTmWith vs (I.App e1 e2) = N.App (injectTmWith vs e1) (injectTmWith vs e2)
injectTmWith vs (I.Unit)      = N.Pair []
injectTmWith vs (I.Pair e1 e2)= N.Pair [injectTmWith vs e1, injectTmWith vs e2]
injectTmWith vs (I.Inj i e)   = N.Inj i (injectTmWith vs e)
-- MatchUnit: the body has no new binders
injectTmWith vs (I.MatchUnit e1 e2) =
    N.Case (injectTmWith vs e1) [(N.unitTm, injectTmWith vs e2)]
-- MatchPair: two new variables are introduced; extend the context twice
injectTmWith vs (I.MatchPair e1 e2) =
    N.Case (injectTmWith vs e1) [(N.Pair [N.Var s1, N.Var s2], injectTmWith vs' e2')]
    where s1    = freshen (show (names ! FZ)) vs
          s2    = freshen (show (names ! FS FZ)) (s1 ::: vs)
          names = I.getLocalName2 e2
          e2'   = I.getBody2 e2
          vs'   = s2 ::: s1 ::: vs
-- MatchSum: each branch introduces one new variable
injectTmWith vs (I.MatchSum e e1 e2) =
    N.Case (injectTmWith vs e)
        [ (N.Inj 0 (N.Var s1), injectTmWith (s1 ::: vs) (I.getBody1 e1))
        , (N.Inj 1 (N.Var s2), injectTmWith (s2 ::: vs) (I.getBody1 e2)) ]
    where s1 = freshen (show (I.getLocalName e1)) vs
          s2 = freshen (show (I.getLocalName e2)) vs

-- | Convert a closed well-scoped term to a named term.
-- Variable names are taken from the 'I.LocalName' hints stored in binders.
injectTm :: I.Tm Z -> N.Tm
injectTm = injectTmWith VNil

-- | Convert a named term to a well-scoped term in scope @n@, given an
-- association list mapping in-scope variable names to their de Bruijn
-- indices.  Each binder prepends a new entry and shifts all existing
-- indices up by one.  Returns @Nothing@ if a free variable is
-- encountered or if the term uses syntactic forms not supported by the
-- simple language (e.g. n-ary patterns).
projectTmWith :: [(String, Fin n)] -> N.Tm -> Maybe (I.Tm n)
-- A variable must be in scope; fail if it is free
projectTmWith vs (N.Var v) = do
    x <- lookup v vs
    return $ I.Var x
-- λ-abstraction: extend the scope with the bound name
projectTmWith vs (N.Lam v b) = do
    b' <- projectTmWith ((v, FZ) : map (fmap FS) vs) b
    return $ I.Lam (I.bind1 (I.LocalName v) b')
projectTmWith vs (N.App f a) = do
    f' <- projectTmWith vs f
    a' <- projectTmWith vs a
    return $ I.App f' a'
-- Empty tuple () maps to Unit
projectTmWith vs (N.Pair []) = return $ I.Unit
-- Binary tuple maps to Pair
projectTmWith vs (N.Pair [e1,e2]) = I.Pair <$> projectTmWith vs e1 <*> projectTmWith vs e2
-- Only injections 0 and 1 are supported
projectTmWith vs (N.Inj i e1) | i == 0 || i == 1 = I.Inj i <$> projectTmWith vs e1
-- case e of { () -> e' }  maps to MatchUnit
projectTmWith vs (N.Case e [(N.Pair [], e1)]) =
    I.MatchUnit <$> projectTmWith vs e <*> projectTmWith vs e1
-- case e of { (v1, v2) -> e' }  maps to MatchPair
-- v2 is innermost (FZ), v1 is next (FS FZ)
projectTmWith vs (N.Case e [(N.Pair [N.Var v1, N.Var v2], e1)]) = do
    a' <- projectTmWith vs e
    b' <- projectTmWith ((v2, FZ) : (v1, FS FZ) : map (fmap (FS . FS)) vs) e1
    return (I.MatchPair a' (I.bind2 (I.LocalName v1) (I.LocalName v2) b'))
-- case e of { Inj0 v1 -> e1 ; Inj1 v2 -> e2 }  maps to MatchSum
projectTmWith vs (N.Case e [(N.Inj 0 (N.Var v1), e1), (N.Inj 1 (N.Var v2), e2)]) = do
    a'  <- projectTmWith vs e
    b1' <- projectTmWith ((v1, FZ) : map (fmap FS) vs) e1
    b2' <- projectTmWith ((v2, FZ) : map (fmap FS) vs) e2
    return (I.MatchSum a' (I.bind1 (I.LocalName v1) b1')
                          (I.bind1 (I.LocalName v2) b2'))
-- Any other pattern is not supported
projectTmWith vs _ = Nothing

-- | Convert a named term to a closed well-scoped term.
-- Returns @Nothing@ if the named term contains free variables or uses
-- syntactic forms not supported by the simple language (e.g. n-ary patterns).
projectTm :: N.Tm -> Maybe (I.Tm Z)
projectTm = projectTmWith []

------------------------------------------------------------------------
-- * Round-trip properties
------------------------------------------------------------------------

-- | Injecting a scoped term into named form and projecting back yields
-- the original term.
prop_project_round_trip :: I.Tm Z -> Bool
prop_project_round_trip i = projectTm ((injectTm i) :: N.Tm) == Just i

-- | Pretty-printing a term and parsing it back yields the original named term.
prop_parse_round_trip :: I.Tm Z -> Bool
prop_parse_round_trip i = N.parseTm (show (N.test (injectTm i :: N.Tm))) == Right (injectTm i)
