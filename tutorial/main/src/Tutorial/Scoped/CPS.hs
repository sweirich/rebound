{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-|
Module      : Simple.CPS
Description : Call-by-value CPS translation for the simply-typed lambda calculus

This module implements a standard call-by-value CPS translation.  

The translation is defined by the following equations, where @[[e]] k@ means
"translate @e@, passing results to continuation @k@":

@
[[x]]                        k = k x
[[λx. e]]                    k = k (λx. λk'. [[e]] k')
[[e1 e2]]                    k = [[e1]] (λx. [[e2]] (λy. x y k))
[[()]]                       k = k ()
[[(e1, e2)]]                 k = [[e1]] (λx. [[e2]] (λy. k (x,y)))
[[inj i e]]                  k = [[e]] (λx. k (inj i x))
[[case e of () -> b]]      k = [[e]] (λz. case z of () -> [[b]] k)
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


wk :: Env Tm n (S n)
wk = shift1E


-- | The default name used for fresh continuation variables.
kN :: LocalName
kN = LocalName "k"

-- | Identity function  "\x.x"
idTm :: Tm Z
idTm = Lam (bind1 (LocalName "x") (Var FZ))

isFirstOrder :: Tm n -> Bool
isFirstOrder (Var x) = True
isFirstOrder Unit = True
isFirstOrder (Pair v1 v2) = isFirstOrder v1 && isFirstOrder v2
isFirstOrder (Inj i v) = isFirstOrder v
isFirstOrder _ = False

------------------------------------------------------------------------
-- * Top-level entry point and properties
------------------------------------------------------------------------

-- | Apply the CPS translation to a closed term, using the identity
-- continuation @λx. x@ so that the result is still a closed term.
cps :: Tm Z -> Tm Z
cps e = cpsExp idE e idTm



-- | __Correctness__: CPS preserves big-step evaluation
--
-- @eval(e) == eval(cps(e))@
--
-- If the result of eval(e) contains a function, then this is not true
prop_cps_result :: Property
prop_cps_result = forAll genFull $ \ e ->
      let cps_e      = cps e
          eval_e     = eval e 
          eval_cps_e = eval (cps_e)
       in
         counterexample ("e          = " ++ pp e)          $
         counterexample ("cps_e      = " ++ pp cps_e)      $
         eval_e == eval_cps_e


-- If the result of eval(e) contains a function, then this is not true
-- so we discard all such cases
prop_cps_result_firstorder :: Property
prop_cps_result_firstorder = forAll genTypedFull $ \e ->
    let
       cps_e = cps e
       eval_e = case eval e of
                 Nothing -> discard
                 Just v -> if isFirstOrder v then v else discard 
       eval_cps_e = case eval cps_e of
                    Nothing -> discard
                    Just v -> v 
    in
      counterexample ("e          = " ++ pp e)          $
      counterexample ("eval_e     = " ++ pp eval_e)     $
      counterexample ("cps_e      = " ++ pp cps_e)      $
      counterexample ("eval_cps_e = " ++ pp eval_cps_e) $
      eval_e == eval_cps_e


------------------------------------------------------------------------------
-- 
-- 
-- big-step simulation:
--           e  =>  v 
--           |      |
--        cps e => cps v
--
--   we can write this property succinctly as:
--      eval (cps e) = cps (eval e) 
--
-- NB: this is not true because the cps conversion of a value is not 
-- a value
prop_cps_eval_simulates :: Property
prop_cps_eval_simulates = forAll genTypedFull $ \e ->
       counterexample ("e          = " ++ pp e)          $
       counterexample ("cps_e      = " ++ pp (cps e))    $
       eval (cps e) == (cps <$> eval e)   -- lift cps over Maybe type

-- alternative: if we use a "fresh variable" instead of the id function
-- this property is true for pure lambda calculus terms. But it still 
-- fails for the full language.
prop_cps_eval_simulates_open :: Property
prop_cps_eval_simulates_open = forAll genTypedPureLC $ \e ->
   let 
      pp' = ppWith ("k" ::: VNil)
      cps_e = cpsExp zeroE e (Var FZ)
      eval_e = case reduce e of
                 Nothing -> discard -- should be impossible for well-typed terms
                 Just v -> v 
      cps_eval_e = cpsExp zeroE eval_e (Var FZ) 
      eval_cps_e = case reduce (cps_e) of
                    Nothing -> discard
                    Just v -> v
    in
       counterexample ("e          = " ++ pp e)          $
       counterexample ("eval_e     = " ++ pp eval_e)     $
       counterexample ("cps_e      = " ++ pp' cps_e)      $
       counterexample ("cps_eval_e = " ++ pp' cps_eval_e) $
       counterexample ("eval_cps_e = " ++ pp' eval_cps_e) $
       eval_cps_e == cps_eval_e



-- | __Simulation__ : CPS preserves small-step evaluation
--
--     if    e -> e'
--     then  cps e -> cps e'
--                        
prop_cps_step :: Tm Z -> Property
prop_cps_step e =
     counterexample ("e      = " ++ pp e) $
     counterexample ("e'     = " ++ pp e') $
     counterexample ("cps_e  = " ++ pp cps_e) $
     counterexample ("cps_e' = " ++ pp cps_e') $
     cps_e == cps_e'
  where
     cps_e = cps e
     e' = case step e of
            Left _ -> discard -- if e does not step, ignore this test
            Right v -> v
     cps_e' = cps e'

-- | __Simulation__ : CPS preserves small-step evaluation
--
--     if    e -> e'
--     then  cps e ->* cps e'
--                        
prop_cps_steps :: Tm Z -> Property
prop_cps_steps e =
     counterexample ("e      = " ++ pp e) $
     counterexample ("e'     = " ++ pp e') $
     counterexample ("cps_e  = " ++ pp cps_e) $
     counterexample ("cps_e' = " ++ pp cps_e') $
     step_star VNil cps_e cps_e'
  where
     cps_e = cps e
     e' = case step e of
            Left _ -> discard -- if e does not step, ignore this test
            Right v -> v
     cps_e' = cps e'

     
-- | does e ->* e' hold?     
step_star :: Vec n String -> Tm n -> Tm n -> Property
step_star vv e e' = 
    counterexample ("steps to  => " ++ ppWith vv e) $
    e == e' .||. case step e of 
                    Left _ -> property False  -- e should not get stuck
                    Right e1 -> step_star vv e1 e'


------------------------------------------------------------------------
-- * CBV CPS translation 
------------------------------------------------------------------------

cpsExp :: forall n m. Env Tm n m -> Tm n -> Tm m -> Tm m
cpsExp r (Var x) k = App k (applyEnv r x)
cpsExp r Unit k    = App k Unit
cpsExp r (Lam b) k = App k 
    (Lam (bind1 (getLocalName b) 
      (Lam (bind1 (LocalName "k")
          (cpsExp r' (getBody b) (Var FZ))))))
    where 
        r' = up r .>> wk
cpsExp r (App t1 t2) k = 
    cpsExp r t1 (Lam (bind1 (LocalName "v")
      (cpsExp r' t2 (Lam (bind1 (LocalName "w")
          (App (App (Var (FS FZ)) (Var FZ)) k''))))))  
       where
         r'  = r .>> wk
         k'' = applyE (wk .>> wk) k
cpsExp r (MatchUnit e1 e2) k = 
    cpsExp r e1 (Lam (bind1 (LocalName "v")
       (MatchUnit (Var FZ) 
          (cpsExp r' e2 k'))))
    where
        r' = r .>> wk
        k' = applyE wk k
cpsExp r (Pair t1 t2) k =
    cpsExp r t1 (Lam (bind1 (LocalName "v")
       (cpsExp (skip r) t2 (Lam (bind1 (LocalName "w")
          (App k'' (Pair (Var (FS FZ)) (Var FZ))))))))
      where 
        r' :: Env Tm n (S m)
        r'  = r .>> wk
        k'' :: Tm (S (S m))
        k'' = applyE (wk .>> wk) k
cpsExp r (MatchPair e1 b) k = 
    cpsExp r e1 (Lam (bind1 (LocalName "v1")
      (MatchPair (Var FZ) (bind2 x1 x2 
        (cpsExp (up (up (r .>> wk))) (getBody2 b) k'''))))) 
        where
            names = getLocalName2 b
            x1 = names ! FZ
            x2 = names ! FS FZ
            k''' = applyE (wk .>> wk .>> wk) k
cpsExp r (Inj i e) k = 
    cpsExp r e (Lam (bind1 (LocalName "v")
       (App k' (Inj i (Var FZ))))) 
       where k' = applyE wk k
cpsExp r (MatchSum e0 e1 e2) k = 
    cpsExp r e0 (Lam (bind1 (LocalName "v")
       (MatchSum (Var FZ)
           (bind1 (getLocalName e1)
                  (cpsExp (up (skip r)) (getBody e1) k''))
           (bind1 (getLocalName e2)
                  (cpsExp (up (skip r)) (getBody e2) k'')))))
    where k'' = applyE (wk .>> wk) k


-- Plotkin's solution: the colon translation
-- define the following variant of CPS conversion

cpsVal :: Env Tm m1 m2 -> Tm m1 -> Tm m2
cpsVal r (Var x) = applyEnv r x
cpsVal r Unit = Unit
cpsVal r (Lam b) =  
    (Lam (bind1 (getLocalName b) 
      (Lam (bind1 kN
          (cpsExp (skip (up r)) (getBody b) (Var FZ))))))
cpsVal r (Pair v1 v2) = 
    Pair (cpsVal r v1) (cpsVal r v2)
cpsVal r (Inj i v1) = 
    Inj i (cpsVal r v1)

colon :: Env Tm n1 n2 -> Tm n1 -> Tm n2 -> Tm n2
colon r v k | isVal v = App k (cpsVal r v)
colon r (App v1 v2) k | isVal v1 && isVal v2 = 
    App (App (cpsVal r v1) (cpsVal r v2)) k
colon r (App v1 e2) k | isVal v1 = 
    colon r e2 (Lam (bind1 (LocalName "v2")
                  (App (App v1' (Var FZ)) k')))
    where v1' = applyE wk (cpsVal r v1)
          k'  = applyE wk k
colon r (App e1 e2) k = 
    colon r e1 (Lam (bind1 (LocalName "v1")
                 (colon(r .>> wk) e2
                     (Lam (bind1 (LocalName "v2")
                        (App (App (Var (FS FZ)) (Var FZ)) k'))))))
    where 
        k' = applyE (wk .>> wk) k
colon r (Pair v1 v2) k | isVal v1 && isVal v2 = 
    App k (Pair (cpsVal r v1) (cpsVal r v2))
colon r (Pair v1 e2) k | isVal v1 = 
    colon r e2 (Lam (bind1 (LocalName "v2")
                  (App k' (Pair v1' (Var FZ)))))
    where v1' = applyE wk (cpsVal r v1)
          k'  = applyE wk k
colon r (Pair e1 e2) k = 
    colon r e1 (Lam (bind1 (LocalName "v1")
                 (cpsExp (r .>> wk) e2
                     (Lam (bind1 (LocalName "v2")
                        (App k' (Pair (Var (FS FZ)) (Var FZ))))))))
    where 
        k' = applyE (wk .>> wk) k
colon r (Inj i v1) k | isVal v1 = 
    App k (Inj i (cpsVal r v1))
colon r (Inj i e1) k =
    colon r e1 (Lam (bind1 (LocalName "v2")
                  (App k' (Inj i (Var FZ)))))
    where k'  = applyE wk k
colon r (MatchUnit v1 e2) k | isVal v1 = 
    MatchUnit (cpsVal r v1) (colon r e2 k)
colon r (MatchUnit e1 e2) k = 
    colon r e1 (Lam (bind1 (LocalName "v1")
                    (MatchUnit (Var FZ) (colon r' e2 k'))))
    where r' = r .>> wk
          k' = applyE wk k
colon r (MatchPair v1 e2) k | isVal v1 = 
    MatchPair (cpsVal r v1) 
        (bind2 x y 
           (colon r' (getBody2 e2) k'))
    where
        r' = up (up r)
        k' = applyE (wk .>> wk) k
        names = getLocalName2 e2
        x = names ! FZ
        y = names ! (FS FZ)
colon r (MatchPair e1 b) k = 
    colon r e1 (Lam (bind1 (LocalName "v1")
      (MatchPair (Var FZ) (bind2 x1 x2 
        (colon (up (up (r .>> wk))) (getBody2 b) k'''))))) 
        where
            names = getLocalName2 b
            x1 = names ! FZ
            x2 = names ! FS FZ
            k''' = applyE (wk .>> wk .>> wk) k
colon r (MatchSum v1 e1 e2) k | isVal v1 = 
    (MatchSum (cpsVal r v1)
           (bind1 (getLocalName e1)
                  (colon (up r) (getBody e1) k'))
           (bind1 (getLocalName e2)
                  (colon (up r) (getBody e2) k')))
    where k' = applyE wk k
colon r (MatchSum e0 e1 e2) k = 
    cpsExp r e0 (Lam (bind1 (LocalName "v1")
       (MatchSum (Var FZ)
           (bind1 (getLocalName e1)
                  (colon (up (skip r)) (getBody e1) k''))
           (bind1 (getLocalName e2)
                  (colon (up (skip r)) (getBody e2) k'')))))
    where k'' = applyE (wk .>> wk) k



prop_a :: Tm Z -> Property
prop_a e =  
    step_star ("k" ::: VNil) (cpsExp zeroE e k) (colon zeroE e k) 
       where k = Var FZ
    
prop_b :: Tm Z -> Property
prop_b e = 
      step_star ("k" ::: VNil) (colon zeroE e k) (colon zeroE e' k)
    where
       k = Var FZ 
       e' = case step e of 
               Left _ -> discard
               Right e1 -> e1

prop_plotkin :: Tm Z -> Property
prop_plotkin e = step_star vv cps_e cps_v
    where  
       cps_e = cpsExp zeroE e k
       cps_v = cpsExp zeroE v k
       k = Var FZ
       vv = "k" ::: VNil
       v = case eval e of 
            Nothing -> discard
            Just v1 -> v1

prop_simulation :: Tm Z -> Property
prop_simulation e = step_star vv cps_e cps_e'
   where  
       cps_e = colon zeroE e k
       cps_e' = colon zeroE e' k
       k = Var FZ
       vv = "k" ::: VNil
       e' = case step e of 
            Left _ -> discard
            Right e1 -> e1

------------------------------------------------------------------------
-- * Continuations
------------------------------------------------------------------------

-- | A continuation in scope @n@.  Two representations are maintained to
-- control whether a lambda is emitted in the output term:
--
-- * 'Obj' holds an existing object-level term; applying it emits @App@.
-- * 'Meta' holds a Haskell-level binder; applying it substitutes directly,
--   avoiding an administrative reduction in the output.
data Cont (n :: Nat) where
  -- | An object-level continuation: a term to be applied.
  Obj   :: Tm n          -> Cont n
  -- | A meta-level continuation: a binder to be instantiated.
  Meta  :: Bind1 Tm Tm n -> Cont n
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
-- * CPS translation (One-pass meta/obj continuations)
------------------------------------------------------------------------

-- This translation avoids creating (some) administrative reductions
   
topK :: Tm Z -> Tm (S Z)
topK e = cpsOpt zeroE e (Obj (Var FZ))

top :: Tm Z -> Tm Z
top e = cpsOpt zeroE e (Obj idTm)

cpsOpt :: forall n m. Env Tm n m -> Tm n -> Cont m -> Tm m
cpsOpt r (Var x) k = applyCont k (applyEnv r x)
cpsOpt r Unit k    = applyCont k Unit
cpsOpt r (Lam b) k = applyCont k $ 
    Lam (bind1 (getLocalName b) 
      (Lam (bind1 kN
          (cpsOpt (skip (up r)) (getBody b) (Obj (Var FZ))))))
cpsOpt r (Pair t1 t2) k =
    cpsOpt r t1 (Meta (bind1 (LocalName "v1")
       (cpsOpt r' t2 (Meta (bind1 (LocalName "v2")
          (applyCont k'' (Pair (Var (FS FZ)) (Var FZ))))))))
      where 
        r' :: Env Tm n (S m)
        r'  = r .>> wk
        k'' :: Cont (S (S m))
        k'' = applyE (wk .>> wk) k
cpsOpt r (App t1 t2) k = 
    cpsOpt r t1 (Meta (bind1 (LocalName "v1")
      (cpsOpt r' t2 (Meta (bind1 (LocalName "v2")
          (App (App (Var (FS FZ)) (Var FZ)) (reifyCont k'')))))))  
       where
         r'  = r .>> wk
         k'' = applyE (wk .>> wk) k
cpsOpt r (MatchPair e1 b) k = 
    cpsOpt r e1 (Meta (bind1 (LocalName "v1")
      (MatchPair (Var FZ) (bind2 x1 x2 
        (cpsOpt (up (up (r .>> wk))) (getBody2 b) k'''))))) 
        where
            names = getLocalName2 b
            x1 = names ! FZ
            x2 = names ! FS FZ
            k''' = applyE (wk .>> wk .>> wk) k
cpsOpt r (Inj i e) k = 
    cpsOpt r e (Meta (bind1 (LocalName "v1")
       (applyCont k' (Inj i (Var FZ))))) 
       where k' = applyE wk k
cpsOpt r (MatchUnit e1 e2) k = 
    cpsOpt r e1 (Meta (bind1 (LocalName "v1")
       (MatchUnit (Var FZ) 
          (cpsOpt r' e2 k'))))
    where
        r' = r .>> wk
        k' = applyE wk k
cpsOpt r (MatchSum e0 e1 e2) k = 
    cpsOpt r e0 (Meta (bind1 (LocalName "v1")
       (MatchSum (Var FZ)
           (bind1 (getLocalName e1)
                  (cpsOpt (up (skip r)) (getBody e1) k''))
           (bind1 (getLocalName e2)
                  (cpsOpt (up (skip r)) (getBody e2) k'')))))
    where k'' = applyE (wk .>> wk) k
    

prop_cpsOpt_eval_simulates_open :: Property
prop_cpsOpt_eval_simulates_open = forAll genTypedFull $ \e ->
       counterexample ("e          = " ++ pp e)          $
       counterexample ("cps_e      = " ++ pp (cps e))    $
       reduce (topK e) == (topK <$> reduce e)   -- lift cps over Maybe type

