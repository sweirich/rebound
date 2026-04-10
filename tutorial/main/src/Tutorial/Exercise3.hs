-- Solutions to the exercises in Lecture 3.
-- These solutions use Tutorial.Scoped.Eval and
-- Tutorial.Scoped.Gen.

module Tutorial.Exercise3 where

import Data.Fin
import Data.Vec (Vec(..), (!))
import Test.QuickCheck

import qualified Tutorial.Named.Syntax   as N
import           Tutorial.Scoped.Syntax  as S
import           Tutorial.Scoped.ScopeCheck
import           Tutorial.Scoped.Gen
import           Tutorial.Scoped.Eval    (eval, reduce, isInert, isVal, findBranch)
import qualified Rebound.Bind.Pat as Pat

------------------------------------------------------------------------
-- * Exercise 1: Extending genTm with let
------------------------------------------------------------------------
--
-- After adding Let :: Tm n -> Bind1 Tm Tm n -> Tm n to S.Tm, extend
-- genScopedTm in Tutorial.Scoped.Gen by adding to the Full branch:
--
--   , Let <$> gen <*> gen1
--
-- where gen1 = bind1 @Tm <$> genLocalName <*> genTm l (next n) sz'
-- is already computed for the Lam and MatchSum cases.
--
-- Why gen1 is right:
--   Let e b   has e :: Tm n  (scrutinee, current scope)
--             and b :: Bind1 Tm Tm n  (body under one new binder, scope S n)
--   gen1 generates exactly a Bind1 whose body lives in scope S n.
--   This is the same reason gen1 is used for Lam.
--
-- How Let differs from App:
--   App f a  — both subterms run in the same scope n.
--   Let e b  — scrutinee e runs in scope n; body of b runs in scope S n.
--   The binder introduces one fresh variable FZ visible only inside b.
--
-- prop_project_round_trip still passes after this change because:
--   1. injectTm (Let e b) = N.letTm s (injectTm e) (injectTmWith (s ::: vs) body)
--      which is App (Lam s body') e', fully handled by existing cases.
--   2. projectTm of that named form reconstructs Let e' b' with the same
--      de Bruijn structure, and LocalName equality ignores the freshened name.

------------------------------------------------------------------------
-- * Exercise 5: Open-term round trip
------------------------------------------------------------------------

-- The free variable is named "x0" to match the convention in injectTmWith
-- (just any string will do; see note below).

-- | Round-trip property for terms with one free variable.
--
-- We supply a name "x0" for the single free variable:
--   injectTmWith ("x0" ::: VNil) t   names index FZ as "x0"
--   projectTmWith [("x0", FZ)]        maps "x0" back to FZ
--
-- The choice of name does not matter for correctness: whatever string we
-- use, injectTmWith will emit that string for every occurrence of Var FZ,
-- and projectTmWith will map it back to FZ.  The only requirement is that
-- the same name is used in both calls.
prop_project_round_trip_open :: S.Tm (S Z) -> Bool
prop_project_round_trip_open t =
    let names = "x0" ::: VNil
        named  = injectTmWith names t
        scoped = projectTmWith names named
    in scoped == Right t


------------------------------------------------------------------------
-- * Exercise 5: Substitution laws
------------------------------------------------------------------------

-- | Identity law: applying the identity substitution is a no-op.
prop_idE :: Property
prop_idE = forAll0 Scoped Full $ \t -> applyE @Tm idE t == t

-- | Identity law for open terms (where variables can actually occur).
prop_idE_open :: Property
prop_idE_open = forAll1 Scoped Full $ \t -> applyE @Tm idE t == t

-- | Composition law: applying f after g equals applying compE f g directly.
-- We test with a concrete environment g that closes the one free variable.
-- compE requires the types to line up: g :: Env (S Z) Z,  f :: Env Z Z.
prop_compE :: Property
prop_compE = 
    forAll0 Scoped Full $ \u0 ->
    forAll1 Scoped Full $ \u1 ->
    forAll1 Scoped Full $ \t ->
    let g :: Env Tm N1 N1 
        g = u1 .: zeroE    
        f :: Env Tm N1 N0 
        f = u0 .: idE      
    in applyE f (applyE g t) == applyE (g .>> f) t

weaken :: Tm n -> Tm (S n)
weaken = applyE @Tm shift1E

-- | Instantiate-shift round-trip: instantiating a weakened term is identity.
prop_instantiate_weaken :: Tm Z -> Tm Z -> Bool
prop_instantiate_weaken t u = instantiate1 (bind (LocalName "x") (weaken t)) u == t

