{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-|
Module      : Simple.CPS
Description : Call-by-value CPS translation for the simply-typed lambda calculus

This module implements a standard call-by-value CPS translation.  The
translation is written using *meta-level* continuations ('Meta') to avoid
introducing administrative redexes in the output, and a scope-tracking GADT
('CpsCtx') to keep de Bruijn indices correct as the output scope grows.

The translation is defined by the following equations, where @[[e]] k@ means
"translate @e@, passing results to continuation @k@":

@
[[x]]                        k = k x
[[λx. e]]                    k = k (λx. λk'. [[e]] k')
[[e1 e2]]                    k = [[e1]] (λx. [[e2]] (λy. x y k))
[[()]]                       k = k ()
[[(e1, e2)]]                 k = [[e1]] (λx. [[e2]] (λy. k (x,y)))
[[inj i e]]                  k = [[e]] (λx. k (inj i x))
[[case e of (x,y) → b]]      k = [[e]] (λz. case z of (x,y) → [[b]] k)
[[case e of {inj i → b_i}]]  k = [[e]] (λz. case z of {inj i → [[b_i]] k})
@

The top-level entry point 'cps' uses the identity continuation @λx. x@.
-}
module Tutorial.Scoped.CPS where

import Test.QuickCheck
import Tutorial.Scoped.Syntax
import Data.Vec ( (!) )
import Tutorial.Scoped.Gen
import Tutorial.Scoped.Eval
import Tutorial.Scoped.ScopeCheck

------------------------------------------------------------------------
-- * Top-level entry point and properties
------------------------------------------------------------------------

-- | Apply the CPS translation to a closed term, using the identity
-- continuation @λx. x@ so that the result is still a closed term.
cps :: Tm Z -> Tm Z
cps e = cpsExp CpsStart e (Obj (Lam (bind1 (LocalName "x") (Var FZ))))

-- | __Correctness__: CPS preserves big-step evaluation.
--
-- @cps(eval(e)) == eval(cps(e))@
--
-- Applying CPS to the value of @e@ gives the same result as
-- evaluating the CPS translation of @e@ directly.
-- Terms that get stuck are discarded.
prop_cps_eval :: Tm Z -> Property
prop_cps_eval e =
     counterexample ("e          = " ++ pp e)          $
     counterexample ("eval_e     = " ++ pp eval_e)     $
     counterexample ("cps_e      = " ++ pp cps_e)      $
     counterexample ("cps_eval_e = " ++ pp cps_eval_e) $
     counterexample ("eval_cps_e = " ++ pp eval_cps_e) $
     cps_eval_e == eval_cps_e
  where
     cps_e = cps e
     eval_e = case eval e of
                 Nothing -> discard
                 Just v -> v
     cps_eval_e = cps eval_e
     eval_cps_e = case eval (cps_e) of
                    Nothing -> discard
                    Just v -> v

{-     e -> e'

       [[e]] ->* [[e']]
    
-}                    

prop_cps_step :: Tm Z -> Property
prop_cps_step e =
     counterexample ("e          = " ++ pp e) $
     counterexample ("eval e     = " ++ pp eval_e) $
     counterexample ("step_e     = " ++ pp step_e) $
     counterexample ("cps_step_e = " ++ pp cps_step_e) $
     counterexample ("cps_e      = " ++ pp cps_e) $
     case eval e of 
        Nothing -> discard -- ignore tests for ill-typed terms or values
        Just _  -> step_star cps_e cps_step_e
  where
     cps_e = cps e
     eval_e = case eval e of 
                 Nothing -> discard
                 Just v -> v
     step_e = case step e of
                 Left _ -> discard -- if e is a value or gets stuck, ignore this test
                 Right v -> v
     cps_step_e = cps step_e
     
     
step_star :: Tm Z -> Tm Z -> Property
step_star e v = 
    counterexample ("steps to  => " ++ pp e) $
    e == v .||. case step e of 
    Left _ -> property False  -- should not get stuck
    Right e' -> step_star e' v


step_step :: Tm Z -> Either Outcome (Tm Z)
step_step e = case step e of 
    Left o -> Left o
    Right e' -> step e'

step_step_step :: Tm Z -> Either Outcome (Tm Z)
step_step_step e = case step e of 
    Left o -> Left o
    Right e' -> case step e' of 
        Left o -> Left o
        Right e'' -> step e''

e = MatchUnit (MatchUnit Unit Unit) (Lam (bind1 (LocalName "w") (Var FZ)))

cps_e = cps e
step_e = case step e of Right v -> v

-- >>> pp step_e
-- "(); \955 w. w"

-- >>> 


------------------------------------------------------------------------
-- * Continuations
------------------------------------------------------------------------

-- | The default name used for fresh continuation variables.
contName :: LocalName
contName = LocalName "k"

-- | A continuation in scope @g@.  Two representations are maintained to
-- control whether a lambda is emitted in the output term:
--
-- * 'Obj' holds an existing object-level term; applying it emits @App@.
-- * 'Meta' holds a Haskell-level binder; applying it substitutes directly,
--   avoiding an administrative reduction in the output.
data Cont (g :: Nat) where
  -- | An object-level continuation: a term to be applied.
  Obj   :: Tm g          -> Cont g
  -- | A meta-level continuation: a binder to be instantiated.
  Meta  :: Bind1 Tm Tm g -> Cont g
    deriving (Generic1)

-- | Apply a continuation to a value.
--
-- * @applyCont (Obj  f) v = App f v@          - create an application
-- * @applyCont (Meta k) v = instantiate1 k v@ — direct substitution
applyCont :: Cont g -> Tm g -> Tm g
applyCont (Obj o)  v  = App o v
applyCont (Meta k) v  = instantiate1 k v

-- | Convert a continuation to an object-level term, introducing a lambda
-- for 'Meta' continuations.  Used when a continuation must appear as a
-- value (e.g. the third argument of a translated application).
reifyCont :: Cont g -> Tm g
reifyCont (Obj  o) = o
reifyCont (Meta k) = Lam k

-- | Enables 'applyE' to apply substitution environments to 'Cont' values,
-- which is needed when weakening continuations into larger scopes.
instance Subst Tm Cont where

------------------------------------------------------------------------
-- * Scope-tracking context
------------------------------------------------------------------------

-- | @CpsCtx g g'@ witnesses how de Bruijn indices in source scope @g@
-- map to indices in CPS output scope @g'@.
--
-- The CPS translation enlarges the scope: lambdas gain an extra continuation
-- argument, and intermediate meta-continuations introduce fresh binders.
-- 'CpsCtx' tracks these additions so that 'cpsIdx' can remap variables
-- correctly.
data CpsCtx g g' where

  -- | The empty context: no variables in scope on either side.
  CpsStart :: CpsCtx N0 N0

  -- | Inside the body of a translated lambda @λx. λk'. body@.
  --
  -- The source body has one extra variable (the lambda parameter @x@).
  -- The CPS body has two extra variables: @FZ = k'@ (the new continuation)
  -- and @FS FZ = x@ (the parameter, shifted up by one).
  -- So @x@ (source @FZ@) maps to @FS FZ@; outer variables shift up by two.
  CpsLam  :: CpsCtx g g' -> CpsCtx (S g) (S (S g'))

  -- | Inside the body of a meta-continuation @Meta (bind1 k body)@.
  --
  -- The bound value (at @FZ@) maps to itself.
  -- Outer variables shift up by one (for the new binder).
  CpsMeta :: CpsCtx g g' -> CpsCtx (S g) (S g')

  -- | Inside a case branch body, after the outer scrutinee meta-binder.
  --
  -- The scope is @S (S g')@:
  -- @FZ@ is the branch pattern variable (freshly bound by the case branch),
  -- @FS FZ@ is the scrutinee result (bound by the outer meta-binder).
  --
  -- The source branch body has one extra variable (the pattern variable).
  -- It maps to @FZ@ in the output; outer variables skip the scrutinee and
  -- shift up by two.
  --
  -- Note: 'CpsLift' has the same index mapping as 'CpsLam' but different
  -- semantics — the extra slot at @FS FZ@ is the scrutinee, not a
  -- continuation.
  CpsLift :: CpsCtx g g' -> CpsCtx (S g) (S (S g'))

-- | Map a source de Bruijn index to its position in the CPS output scope.
cpsIdx :: CpsCtx g g' -> Fin g -> Fin g'
cpsIdx CpsStart    v      = case v of {}          -- Fin Z is empty
cpsIdx (CpsLam gg) FZ     = FS FZ                 -- param moves past k'
cpsIdx (CpsLam gg) (FS v) = FS (FS (cpsIdx gg v))
cpsIdx (CpsMeta gg) FZ     = FZ                   -- bound value stays
cpsIdx (CpsMeta gg) (FS v) = FS (cpsIdx gg v)
cpsIdx (CpsLift gg) FZ     = FZ                   -- pattern var stays
cpsIdx (CpsLift gg) (FS v) = FS (FS (cpsIdx gg v))-- outer vars skip scrutinee

-- | Weaken a term or environment by one variable: shifts every free variable
-- up by one, leaving a fresh @FZ@ unused.
weaken :: Env Tm n (S n)
weaken = shift1E

------------------------------------------------------------------------
-- * The CPS translation
------------------------------------------------------------------------

-- | Translate a term in source scope @g@ to CPS, threading results through
-- continuation @k@ in output scope @g'@.
--
-- The 'CpsCtx' argument tracks how source variables map to output positions.
-- 'Meta' continuations are used throughout to avoid administrative redexes;
-- only 'reifyCont' introduces a lambda when an object-level term is required.
cpsExp :: forall g g'. CpsCtx g g' -> Tm g -> Cont g' -> Tm g'

-- Variables and unit: pass the value directly to k.
cpsExp g (Var v) k = applyCont k (Var (cpsIdx g v))
cpsExp g Unit    k = applyCont k Unit

-- Lambda: [[λx. e]] k = k (λx. λk'. [[e]] k')
-- The body is translated with CpsLam (x moves to FS FZ, k' is at FZ).
-- The continuation for the body is Obj (Var FZ) = k'.
cpsExp g (Lam b) k =
    let e' = Lam . bind1 (getLocalName b)
               $ Lam . bind1 contName
                 $ cpsExp (CpsLam g) (getBody1 b) (Obj (Var FZ))
    in applyCont k e'

{-
-- special case for let
cpsExp g (App (Lam b) e) k = 
    cpsExp g e (Meta . bind1 (getLocalName b)
               $ cpsExp (CpsMeta g) (getBody b) (applyE weaken k))
-}
-- Pair: [[(e1,e2)]] k = [[e1]] (λx. [[e2]] (λy. k (x,y)))
-- k1 evaluates e2 in the extended scope (weaken e2 for the x binder).
-- k2 collects x = Var (FS FZ) and y = Var FZ, forms the pair, passes to k.
cpsExp g (Pair e1 e2) k =
    let k1 :: Cont g'
        k1 = Meta . bind1 contName $ cpsExp (CpsMeta g) (applyE weaken e2) k2
        k2 :: Cont (S g')
        k2 = Meta . bind1 contName $ applyCont k' (Pair (Var (FS FZ)) (Var FZ))
        k' = applyE (weaken .>> weaken) k   -- k weakened past x and y
    in cpsExp g e1 k1

-- Application: [[e1 e2]] k = [[e1]] (λx. [[e2]] (λy. x y k))
-- k1 evaluates e2 after e1.  k2 applies x to y, forwarding to k.
-- k must be reified to an object-level term for the application.
cpsExp g (App e1 e2) k =
    let k1 :: Cont g'
        k1 = Meta . bind1 contName $
               cpsExp (CpsMeta g) (applyE weaken e2) k2
        k2 :: Cont (S g')
        k2 = Meta . bind1 contName $
               App (App (Var (FS FZ)) (Var FZ))           -- x y
                   (reifyCont (applyE (weaken .>> weaken) k))  -- k
    in cpsExp g e1 k1

-- MatchPair: [[case e of (x,y) → b]] k = [[e]] (λz. case z of (x,y) → [[b]] k)
-- The branch body b (in scope S(S g)) is translated with CpsMeta (CpsMeta g)
-- (both x and y map to themselves) and then re-wrapped in bind2.
-- The whole MatchPair is placed inside a meta-binder for the scrutinee z.
cpsExp g (MatchPair e1 b) k =
    let b'    = getBody2 b
        names = getLocalName2 b
        x1    = names ! FZ
        x2    = names ! FS FZ
        -- CpsMeta twice: both x and y stay at their positions
        b''   = bind2 x1 x2 (cpsExp (CpsMeta (CpsMeta g)) b' k')
        -- k weakened past x and y (two binders inside the branch)
        k'    = applyE (weaken .>> weaken) k
        -- The MatchPair lives inside a meta-binder for z (= Var FZ);
        -- weaken b'' once to account for the z binder.
        k1    = Meta . bind1 contName $
                  MatchPair (Var FZ) (applyE weaken b'')
    in cpsExp g e1 k1

-- Injection: [[inj i e]] k = [[e]] (λx. k (inj i x))
-- Evaluate e; wrap the result in Inj i; pass to k.
-- k is weakened once for the x binder.
cpsExp g (Inj i e) k =
    cpsExp g e (Meta . bind1 contName $
        applyCont (applyE weaken k) (Inj i (Var FZ)))

-- MatchUnit: [[case e of () → b]] k = [[e]] (λz. case z of () → [[b]] k)
-- The body b is translated in the extended scope (CpsMeta g).
-- Both b and k are weakened once for the z binder.
cpsExp g (MatchUnit e1 e2) k =
    cpsExp g e1 (Meta . bind1 contName $
        MatchUnit (Var FZ)
            (cpsExp (CpsMeta g) (applyE weaken e2) (applyE weaken k)))

-- MatchSum: [[case e of {inj i y_i → b_i}]] k
--         = [[e]] (λz. case z of {inj i y_i → [[b_i]] k})
-- Each branch body b_i (in scope S g, with y_i at FZ) is translated
-- using CpsLift g: y_i stays at FZ, outer vars skip the scrutinee at FS FZ.
-- k is weakened twice (past z and y_i).
cpsExp g (MatchSum e0 e1 e2) k =
    cpsExp g e0 (Meta . bind1 (LocalName "x") $
        MatchSum (Var FZ)
            (bind1 (getLocalName e1)
                (cpsExp (CpsLift g) (getBody e1)
                    (applyE (weaken .>> weaken) k)))
            (bind1 (getLocalName e2)
                (cpsExp (CpsLift g) (getBody e2)
                    (applyE (weaken .>> weaken) k))))

------------------------------------------------------------------------
-- * Naive CPS translation (object-level continuations only)
------------------------------------------------------------------------

-- | Apply the naive CPS translation to a closed term, using the identity
-- continuation @λx. x@ as an explicit object-level term.
--
-- Unlike 'cps', every intermediate continuation here is a genuine lambda in
-- the output term, not a Haskell-level binder.  The output therefore contains
-- more administrative beta-redexes, but the evaluator reduces them all away,
-- so @eval (cpsObj e) == eval (cps e)@ (see 'prop_cpsObj_eval').
cpsObj :: Tm Z -> Tm Z
cpsObj e = cpsObjExp CpsStart e (Lam (bind1 (LocalName "x") (Var FZ)))

-- | Naive CPS worker.  Translate source term @e@ in scope @g@, applying the
-- /object-level/ continuation @k :: Tm g'@ to the result.
--
-- The equations mirror the standard call-by-value CPS translation verbatim:
--
-- @
-- T[[x]]                   k = k x
-- T[[λx. e]]               k = k (λx. λk'. T[[e]] k')
-- T[[e1 e2]]               k = T[[e1]] (λx. T[[e2]] (λy. x y k))
-- T[[()]]                  k = k ()
-- T[[(e1,e2)]]             k = T[[e1]] (λx. T[[e2]] (λy. k (x,y)))
-- T[[inj i e]]             k = T[[e]] (λx. k (inj i x))
-- T[[case e of () → b]]    k = T[[e]] (λz. case z of () → T[[b]] k)
-- T[[case e of (x,y) → b]] k = T[[e]] (λz. case z of (x,y) → T[[b]] k)
-- T[[case e of {Inj_i y_i → b_i}]] k
--                          = T[[e]] (λz. case z of {Inj_i y_i → T[[b_i]] k})
-- @
cpsObjExp :: forall g g'. CpsCtx g g' -> Tm g -> Tm g' -> Tm g'

-- Variable / Unit: apply k to the (remapped) value.
cpsObjExp g (Var v) k = App k (Var (cpsIdx g v))
cpsObjExp g Unit    k = App k Unit

-- Lambda: T[[λx. e]] k = k (λx. λk'. T[[e]] k')
-- k' is the innermost variable (Var FZ) in the doubly-extended output scope.
cpsObjExp g (Lam b) k =
    let body = cpsObjExp (CpsLam g) (getBody1 b) (Var FZ)
        lam  = Lam . bind1 (getLocalName b) $
                 Lam . bind1 contName $ body
    in App k lam

-- Application: T[[e1 e2]] k = T[[e1]] (λx. T[[e2]] (λy. x y k))
cpsObjExp g (App e1 e2) k =
    let -- λy. x y k   in scope S(S g')
        innerCont = Lam . bind1 (LocalName "y") $
                      App (App (Var (FS FZ)) (Var FZ))
                          (applyE (weaken .>> weaken) k)
        -- λx. T[[e2]] innerCont   in scope g'
        outerCont = Lam . bind1 (LocalName "x") $
                      cpsObjExp (CpsMeta g) (applyE weaken e2) innerCont
    in cpsObjExp g e1 outerCont

-- Pair: T[[(e1,e2)]] k = T[[e1]] (λx. T[[e2]] (λy. k (x,y)))
cpsObjExp g (Pair e1 e2) k =
    let innerCont = Lam . bind1 (LocalName "y") $
                      App (applyE (weaken .>> weaken) k)
                          (Pair (Var (FS FZ)) (Var FZ))
        outerCont = Lam . bind1 (LocalName "x") $
                      cpsObjExp (CpsMeta g) (applyE weaken e2) innerCont
    in cpsObjExp g e1 outerCont

-- Injection: T[[inj i e]] k = T[[e]] (λx. k (inj i x))
cpsObjExp g (Inj i e) k =
    cpsObjExp g e (Lam . bind1 (LocalName "x") $
                       App (applyE weaken k) (Inj i (Var FZ)))

-- MatchUnit: T[[case e of () → b]] k = T[[e]] (λz. case z of () → T[[b]] k)
cpsObjExp g (MatchUnit e1 e2) k =
    cpsObjExp g e1 (Lam . bind1 (LocalName "z") $
                       MatchUnit (Var FZ)
                           (cpsObjExp (CpsMeta g) (applyE weaken e2)
                                                  (applyE weaken k)))

-- MatchPair: T[[case e of (x,y) → b]] k = T[[e]] (λz. case z of (x,y) → T[[b]] k)
-- Build the translated branch body first (k weakened for x and y),
-- then wrap in λz and weaken once more for the scrutinee binder.
cpsObjExp g (MatchPair e1 b) k =
    let b'    = getBody2 b
        names = getLocalName2 b
        x1    = names ! FZ
        x2    = names ! FS FZ
        b''   = bind2 x1 x2
                    (cpsObjExp (CpsMeta (CpsMeta g)) b'
                               (applyE (weaken .>> weaken) k))
    in cpsObjExp g e1 (Lam . bind1 (LocalName "z") $
                          MatchPair (Var FZ) (applyE weaken b''))

-- MatchSum: T[[case e of {Inj_i y_i → b_i}]] k
--         = T[[e]] (λz. case z of {Inj_i y_i → T[[b_i]] k})
-- k weakened twice inside each branch (once for z, once for y_i).
cpsObjExp g (MatchSum e0 e1 e2) k =
    cpsObjExp g e0 (Lam . bind1 (LocalName "z") $
                       MatchSum (Var FZ)
                           (bind1 (getLocalName e1)
                               (cpsObjExp (CpsLift g) (getBody e1)
                                          (applyE (weaken .>> weaken) k)))
                           (bind1 (getLocalName e2)
                               (cpsObjExp (CpsLift g) (getBody e2)
                                          (applyE (weaken .>> weaken) k))))

-- | __Correctness__: naive CPS preserves big-step evaluation.
--
-- @eval(cpsObj(e)) == eval(cpsObj(eval(e)))@
--
-- Unlike 'cps', @cpsObj@ introduces administrative beta-redexes even inside
-- values, so @cpsObj(v)@ is not itself a value.  We therefore evaluate both
-- sides.  Terms that get stuck are discarded.
prop_cpsObj_eval :: Tm Z -> Property
prop_cpsObj_eval e =
     counterexample ("e                    = " ++ pp e)                    $
     counterexample ("eval_e               = " ++ pp eval_e)               $
     counterexample ("eval_cpsObj_e        = " ++ pp eval_cpsObj_e)        $
     counterexample ("eval_cpsObj_eval_e   = " ++ pp eval_cpsObj_eval_e)   $
     eval_cpsObj_e == eval_cpsObj_eval_e
  where
     eval_e = case eval e of
                 Nothing -> discard
                 Just v  -> v
     eval_cpsObj_e = case eval (cpsObj e) of
                       Nothing -> discard
                       Just v  -> v
     eval_cpsObj_eval_e = case eval (cpsObj eval_e) of
                            Nothing -> discard
                            Just v  -> v
