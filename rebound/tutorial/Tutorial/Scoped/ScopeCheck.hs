{-|
Module      : Simple.ScopeCheck
Description : Conversion between the scoped (de Bruijn) and named representations

This module provides two pairs of conversion functions:

* 'injectTy' / 'projectTy' — convert between the simple binary type language
  (@I.Ty@) and the n-ary named type language (@N.Ty@).

* 'injectTm' / 'projectTm' — convert between well-scoped de Bruijn terms
  (@I.Tm n@) and unscoped named terms (@N.Tm@).

The named representation is used for parsing and pretty-printing; the scoped
representation is used for evaluation and type-checking.  The two directions
serve different purposes:

* __inject__ (scoped → named): always succeeds; used for display.
* __project__ (named → scoped): can fail; used after parsing.

-}
module Tutorial.Scoped.ScopeCheck (
  -- * Type conversions
  injectTy,
  projectTy,
  -- * Naming contexts
  Ctx,
  emptyCtx,
  (+%),
  vname,
  -- * Term conversions
  injectTm,
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
import Data.Vec ((!))
import qualified Rebound as Rebound

import qualified Tutorial.Named.Syntax as N
import qualified Tutorial.Named.PP as N
import qualified Tutorial.Named.Parser as N
import qualified Tutorial.Scoped.Syntax as I
import Tutorial.Scoped.Gen
import Tutorial.Lib


import qualified Tutorial.Named.PP as PP

-- | Pretty-print a closed term via the Named pretty printer
pp :: I.Tm Z -> String
pp = PP.pp . injectTm

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
-- * Naming contexts
------------------------------------------------------------------------

-- | A naming context: maps de Bruijn indices in scope @n@ to variable names.
type Ctx n = Fin n -> String

-- | The empty context, with domain @Fin Z@ (no variables in scope).
emptyCtx :: Ctx Z
emptyCtx = \x -> case x of {}

-- | Extend a context with a fresh name for the new outermost variable.
-- The existing names are shifted up by one.
(+%) :: Ctx n -> String -> Ctx (S n)
(+%) g a = \x -> case x of { FZ -> a ; FS y -> g y }

-- | Generate a default variable name from a de Bruijn level.
-- Used as a fallback when a binder carries no user-chosen name.
vname :: SNat n -> String
vname n = "x" ++ show (toInt n)

------------------------------------------------------------------------
-- * Term conversions
------------------------------------------------------------------------

-- | Convert a closed well-scoped term to a named term, using the
-- variable names stored in binders by 'I.LocalName'.
--
-- The helper @to@ carries a 'Ctx' that maps each in-scope de Bruijn index
-- to the name introduced by its binder.  At each binder site the context
-- is extended with the binder's stored name before recursing into the body.
injectTm :: I.Tm Z -> N.Tm
injectTm = to emptyCtx where
        to :: forall n. SNatI n => Ctx n -> I.Tm n -> N.Tm
        to vs (I.Var x)     = N.Var (vs x)
        to vs (I.Lam t)     = N.Lam s (to (vs +% s) (I.getBody1 t))
                                where s = show (I.getLocalName t)
        to vs (I.App e1 e2) = N.App (to vs e1) (to vs e2)
        to vs (I.Unit)      = N.Pair []
        to vs (I.Pair e1 e2)= N.Pair [to vs e1, to vs e2]
        to vs (I.Inj i e)   = N.Inj i (to vs e)
        -- MatchUnit: the body has no new binders
        to vs (I.MatchUnit e1 e2) =
            N.Case (to vs e1) [(N.unitTm, to vs e2)]
        -- MatchPair: two new variables are introduced; extend the context twice
        to vs (I.MatchPair e1 e2) =
            N.Case (to vs e1) [(N.Pair [N.Var s1, N.Var s2], to vs' e2')]
            where s1    = show (names ! FZ)
                  s2    = show (names ! FS FZ)
                  names = I.getLocalName2 e2
                  e2'   = I.getBody2 e2
                  vs'   = (vs +% s1) +% s2
        -- MatchSum: each branch introduces one new variable
        to vs (I.MatchSum e e1 e2) =
            N.Case (to vs e)
                [ (N.Inj 0 (N.Var s1), to (vs +% s1) (I.getBody1 e1))
                , (N.Inj 1 (N.Var s2), to (vs +% s2) (I.getBody1 e2)) ]
            where s1 = show (I.getLocalName e1)
                  s2 = show (I.getLocalName e2)
        to vs (I.Ann e ty)  = N.Ann (to vs e) (injectTy ty)

-- | Convert a named term to a closed well-scoped term.
-- Returns @Nothing@ if the named term contains free variables or uses
-- syntactic forms not supported by the simple language (e.g. n-ary patterns).
--
-- The helper @to@ carries an association list mapping variable names to
-- the de Bruijn index they are bound to in the current scope.  Each binder
-- prepends a new entry and shifts all existing indices up by one.
projectTm :: N.Tm -> Maybe (I.Tm Z)
projectTm = to [] where
        to :: [(String, Fin n)] -> N.Tm -> Maybe (I.Tm n)
        -- A variable must be in scope; fail if it is free
        to vs (N.Var v) = do
            x <- lookup v vs
            return $ I.Var x
        -- λ-abstraction: extend the scope with the bound name
        to vs (N.Lam v b) = do
            b' <- to ((v, FZ) : map (fmap FS) vs) b
            return $ I.Lam (I.bind1 (I.LocalName v) b')
        to vs (N.App f a) = do
            f' <- to vs f
            a' <- to vs a
            return $ I.App f' a'
        -- Empty tuple () maps to Unit
        to vs (N.Pair []) = return $ I.Unit
        -- Binary tuple maps to Pair
        to vs (N.Pair [e1,e2]) = I.Pair <$> to vs e1 <*> to vs e2
        -- Only injections 0 and 1 are supported
        to vs (N.Inj i e1) | i == 0 || i == 1 = I.Inj i <$> to vs e1
        -- case e of { () -> e' }  maps to MatchUnit
        to vs (N.Case e [(N.Pair [], e1)]) =
            I.MatchUnit <$> to vs e <*> to vs e1
        -- case e of { (v1, v2) -> e' }  maps to MatchPair
        -- v2 is innermost (FZ), v1 is next (FS FZ)
        to vs (N.Case e [(N.Pair [N.Var v1, N.Var v2], e1)]) = do
            a' <- to vs e
            b' <- to ((v2, FZ) : (v1, FS FZ) : map (fmap (FS . FS)) vs) e1
            return (I.MatchPair a' (I.bind2 (I.LocalName v1) (I.LocalName v2) b'))
        -- case e of { Inj0 v1 -> e1 ; Inj1 v2 -> e2 }  maps to MatchSum
        to vs (N.Case e [(N.Inj 0 (N.Var v1), e1), (N.Inj 1 (N.Var v2), e2)]) = do
            a'  <- to vs e
            b1' <- to ((v1, FZ) : map (fmap FS) vs) e1
            b2' <- to ((v2, FZ) : map (fmap FS) vs) e2
            return (I.MatchSum a' (I.bind1 (I.LocalName v1) b1')
                                  (I.bind1 (I.LocalName v2) b2'))
        -- Any other pattern is not supported
        to vs _ = Nothing

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
