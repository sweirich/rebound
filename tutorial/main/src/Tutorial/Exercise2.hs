module Tutorial.Exercise2 where

import Data.Fin
import Data.Vec (Vec(..), (!))

import qualified Tutorial.Named.Syntax   as N
import           Tutorial.Scoped.Syntax  as S
import           Tutorial.Scoped.ScopeCheck
import           Tutorial.Scoped.Eval    (eval, reduce, isInert, isVal, findBranch)



------------------------------------------------------------------------
-- * Exercise 1: Tracing projectTmWith
------------------------------------------------------------------------
--
-- Trace 1: projectTm (N.Lam "x" (N.Lam "y" (N.Var "x")))
--
-- Call 1: projectTmWith [] (N.Lam "x" (N.Lam "y" (N.Var "x")))
--   → extend scope: vs = [("x", FZ)]
--
-- Call 2: projectTmWith [("x", FZ)] (N.Lam "y" (N.Var "x"))
--   → extend scope: vs = [("y", FZ), ("x", FS FZ)]
--     (every existing entry gets its index shifted up by FS)
--
-- Call 3: projectTmWith [("y", FZ), ("x", FS FZ)] (N.Var "x")
--   → lookup "x" finds FS FZ
--   → return S.Var (FS FZ)
--
-- Assembling back up:
--   inner Lam body = S.Var (FS FZ) :: S.Tm (S (S Z))
--   outer Lam body = S.Lam (S.bind1 (S.LocalName "y") (S.Var (FS FZ))) :: S.Tm (S Z)
--   result         = S.Lam (S.bind1 (S.LocalName "x") (...))            :: S.Tm Z


ex1_result1 :: Either ScopeCheckError (S.Tm Z)
ex1_result1 = projectTm (N.Lam "x" (N.Lam "y" (N.Var "x")))

-- >>> ex1_result1
-- Right (Lam (bind1 (Lam (bind1 (Var 1)))))


-- The expected de Bruijn term:
--   λ. λ. 1          (x is one binder away)
ex1_expected1 :: S.Tm Z
ex1_expected1 = S.Lam (S.bind (S.LocalName "x")
                  (S.Lam (S.bind (S.LocalName "y")
                    (S.Var (FS FZ)))))

-- >>> ex1_expected1
-- Lam (bind1 (Lam (bind1 (Var 1))))

-- Verify:
ex1_check1 :: Bool
ex1_check1 = ex1_result1 == Right ex1_expected1

-- >>> ex1_check1
-- True

-- ---------------------------------------------------------------------------
--
-- Trace 2: projectTm (N.Case (N.Var "p") [(N.Pair [N.Var "x", N.Var "y"], N.Var "x")])
--
-- This matches the MatchPair case in projectTmWith:
--   case e of { (v1, v2) -> body }
--   where v1 = "x", v2 = "y"
--
-- The rule (from ScopeCheck.hs):
--   b' <- projectTmWith ((v2, FZ) : (v1, FS FZ) : map (fmap (FS . FS)) vs) e1
--
-- So inside the body:
--   vs = [("y", FZ), ("x", FS FZ), ("p", FS (FS FZ))]
--   "y" maps to FZ  (second component, innermost)
--   "x" maps to FS FZ (first component)
--
-- Looking up "x" in the body gives FS FZ.
--
-- Answer: "y" maps to FZ; "x" maps to FS FZ.
-- The convention matches instantiate2 in Eval.hs:
--   instantiate2 bnd v1 v2 maps FS FZ → v1 (first component) and FZ → v2 ...

ex1_result2 :: Either ScopeCheckError (S.Tm Z)
ex1_result2 = projectTm
    (N.Case (N.Var "p")
        [(N.Pair [N.Var "x", N.Var "y"], N.Var "x")])

-- >>> ex1_result2
-- Left (UnboundVariable "p")


-- With "p" in scope (scope S Z):
ex1_result2_open :: Either ScopeCheckError (S.Tm (S Z))
ex1_result2_open = projectTmWith ("p" ::: VNil)
    (N.Case (N.Var "p")
        [(N.Pair [N.Var "x", N.Var "y"], N.Var "x")])

-- >>> ex1_result2_open
-- Right (MatchPair (Var 0) (bind2 (Var 1)))

------------------------------------------------------------------------
-- * Exercise 2: Extending the conversions with let
------------------------------------------------------------------------
--
-- The named representation already encodes let as syntactic sugar:
--   letTm x rhs body = App (Lam x body) rhs
-- So projectTmWith and injectTmWith handle let-expressions automatically
-- through the existing Lam and App cases — no new constructor is needed
-- in N.Tm.
--
-- If we were to add a dedicated S.Let constructor to S.Tm:
--
--   Let :: Tm n -> Bind1 Tm Tm n -> Tm n
--
-- then the new cases would be:
--
-- projectTmWith vs (N.Let v e b) = do
--     e' <- projectTmWith vs e
--     b' <- projectTmWith ((v, FZ) : map (fmap FS) vs) b
--     return $ S.Let e' (S.bind1 (S.LocalName v) b')
--
-- injectTmWith vs (S.Let e b) =
--     N.Let s (injectTmWith vs e) (injectTmWith (s ::: vs) (S.getBody1 b))
--     where s = freshen (show (S.getLocalName b)) vs
--
-- The treatment is identical to Lam in both directions:
--   - project: extend the scope with the bound name (FZ) and shift existing
--     names by FS, exactly as for Lam.
--   - inject: retrieve the stored LocalName hint, freshen it against the
--     current vector, and prepend it before recursing into the body.
-- The only difference is that Let also carries a scrutinee `e` that is
-- translated in the *current* scope (not the extended one), just as in App.
--
-- prop_project_round_trip continues to hold because injectTm produces a
-- named term whose let-binder carries the same LocalName stored by bind1,
-- and projectTmWith assigns the bound variable FZ again, recovering the
-- original de Bruijn term.
