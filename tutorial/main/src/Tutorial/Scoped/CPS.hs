{-|
Module      : Tutorial.Scoped.CPS
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
[[inj i e]]                  k = [[e]]  (λx. k (inj i x))
[[case e of p_i -> b_i]]     k = [[e]]  (λz. case z of p_i -> [[b_i]] k)
@

The top-level entry point uses the identity continuation @λx. x@. We can also 
observe what happens when we use a free variable @k@ for the top-level continuation.
-}
module Tutorial.Scoped.CPS where

import Test.QuickCheck
import Tutorial.Scoped.Syntax
import qualified Rebound.Bind.Pat as Pat
import Data.Vec ( (!) )
import Tutorial.Scoped.Gen
import Tutorial.Scoped.Eval
import Tutorial.Scoped.ScopeCheck


------------------------------------------------------------------------
-- * Top-level entry point 
------------------------------------------------------------------------


-- | Identity function  "\x.x"
idTm :: Tm Z
idTm = Lam (bind1 (LocalName "x") (Var FZ))


-- | Apply the CPS translation to a closed term, using the identity
-- continuation @λx. x@ so that the result is still a closed term.
cps :: Tm Z -> Tm Z
cps e = cpsExp zeroE e idTm

-- | Apply the CPS translation to a closed term, using a variable
-- as the continuation so that the result has one free variable.
cpsK :: Tm Z -> Tm (S Z)
cpsK e = cpsExp zeroE e (Var FZ) 

------------------------------------------------------------------------
-- * CBV CPS translation 
------------------------------------------------------------------------

wk :: Env Tm n (S n)
wk = shift1E

-- [[ \x.x ]] k == k (\x.\k'. k' x)
-- [[ \.0 ]] k == k (\ \ . 0 1)

cpsExp :: forall n m. Env Tm n m -> Tm n -> Tm m -> Tm m
-- [[x]] k = k x
cpsExp r (Var x) k = App k (applyEnv r x)
-- [[()]] k = k ()
cpsExp r Unit k    = App k Unit
-- [[λx. e]] k = k (λx. λk'. [[e]] k')
cpsExp r (Lam b) k = 
    App k (Lam (bind1 (LocalName (name (getLocalName b))) 
            (Lam (bind1 (LocalName "k") (cpsExp r' (getBody b) k')))))
       where r' :: Env Tm (S n) (S (S m))
             r' = up r .>> wk 
             k' :: Tm (S (S m))
             k' = Var FZ
-- [[e1 e2]] k = [[e1]] (λx. [[e2]] (λy. x y k))
cpsExp r (App e1 e2) k = 
    cpsExp r e1 (Lam (bind1 (LocalName "x") 
                       (cpsExp (r .>> wk) e2 (Lam (bind1 (LocalName "y")
                            (App (App (Var (FS FZ)) (Var FZ)) k'))))))
        where k' :: Tm (S (S m))
              k' = applyE (wk .>> wk) k

-- [[(e1, e2)]] k = [[e1]] (λx. [[e2]] (λy. k (x,y)))
cpsExp r (Pair t1 t2) k =
    cpsExp r t1 (Lam (bind1 (LocalName "v")
       (cpsExp (skip r) t2 (Lam (bind1 (LocalName "w")
          (App k'' (Pair (Var (FS FZ)) (Var FZ))))))))
      where 
        r'  = r .>> wk
        k'' = applyE (wk .>> wk) k
cpsExp r (Inj i e) k =
    cpsExp r e (Lam (bind1 (LocalName "v")
       (App k' (Inj i (Var FZ)))))
       where k' = applyE wk k
-- [[case e of { pᵢ -> bᵢ }]] k = [[e]] (λz. case z of { pᵢ -> [[bᵢ]] k' })
cpsExp r (Match e brs) k =
    cpsExp r e (Lam (bind1 (LocalName "z") (Match (Var FZ) (map cpsBranch brs))))
    where
        r' = r .>> wk
        k' = applyE wk k
        cpsBranch :: Branch n -> Branch (S m)
        cpsBranch (Branch b) =
            let pat   = Pat.getPat b
                sz    = size pat
                body' = cpsExp (upN sz r') (Pat.getBody b) (applyE @Tm (shiftNE sz) k')
            in Branch (Pat.bind pat body')

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

-- | CPS preserves big-step evaluation
--
-- @eval(e) == eval(cps(e))@
--      
--  i.e.       e =>  v1     and   [[e]]_id => v2  and   v1 == v2
--         
-- 
-- NB: this is not true, what is a counter example?
prop_cps_result :: Property
prop_cps_result = forAll0 Typed Full $ \ e ->
      let cps_e      = cps e
          eval_e     = eval e 
          eval_cps_e = eval (cps_e)
       in
         counterexample ("e          = " ++ pp e)          $
         counterexample ("cps_e      = " ++ pp cps_e)      $
         eval_e == eval_cps_e

-- | CPS preserves big-step evaluation for *firstorder* values
--
-- If @v = eval(e)@ and v is firstorder then @v == eval(cps(e))@ 
-- 
prop_cps_result_firstorder :: Property
prop_cps_result_firstorder = forAll0 Typed Full $ \e ->
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

-- | a first-order value does not contain any functions
isFirstOrder :: Tm n -> Bool
isFirstOrder (Var x) = True
isFirstOrder Unit = True
isFirstOrder (Pair v1 v2) = isFirstOrder v1 && isFirstOrder v2
isFirstOrder (Inj i v) = isFirstOrder v
isFirstOrder _ = False



------------------------------------------------------------------------------
-- Can we do better for results that include functions? Here is another 
-- property that cps converts the value
-- 
--           e  =>  v 
--           |      |
--        cps e => cps v
--
--   we can write this property succinctly as:
--      eval (cps e) = cps (eval e) 
--
-- NB: this is not true because the cps conversion of a value is not 
-- a value, it is id applied to the translated value
prop_cps_eval_cps :: Property
prop_cps_eval_cps = forAll0 Typed Full $ \e ->
       counterexample ("e          = " ++ pp e)          $
       counterexample ("cps_e      = " ++ pp (cps e))    $
       eval (cps e) == (cps <$> eval e)   -- lift cps over Maybe type

-- alternative: we use a "fresh variable" instead of the id function
-- this property is true for pure lambda calculus terms. But we need to 
-- use reduction instead of evaluation. 
-- NB: this fails for terms that use pattern matching
prop_cps_reduce_cps :: Property
prop_cps_reduce_cps = forAll0 Typed PureLC $ \e ->
   let 
      cps_e = cpsK e 
      eval_e = case reduce e of
                 Nothing -> discard -- should be impossible for well-typed terms
                 Just v -> v 
      cps_eval_e = cpsK eval_e 
      eval_cps_e = case reduce cps_e of
                    Nothing -> discard
                    Just v -> v
      pp' = ppWith ("k" ::: VNil) -- name for index zero
    in
       counterexample ("e          = " ++ pp e)          $
       counterexample ("eval_e     = " ++ pp eval_e)     $
       counterexample ("cps_e      = " ++ pp' cps_e)      $
       counterexample ("cps_eval_e = " ++ pp' cps_eval_e) $
       counterexample ("eval_cps_e = " ++ pp' eval_cps_e) $
       eval_cps_e == cps_eval_e

-- OK: let's just test the property for pure lambda calculus terms
prop_cps_reduce_cps_pure :: Property
prop_cps_reduce_cps_pure = forAll0 Typed PureLC $ \e ->
   let 
      cps_e = cpsK e 
      eval_e = case reduce e of
                 Nothing -> discard -- should be impossible for well-typed terms
                 Just v -> v 
      cps_eval_e = cpsK eval_e 
      eval_cps_e = case reduce cps_e of
                    Nothing -> discard
                    Just v -> v
      pp' = ppWith ("k" ::: VNil)
    in
       counterexample ("e          = " ++ pp e)          $
       counterexample ("eval_e     = " ++ pp eval_e)     $
       counterexample ("cps_e      = " ++ pp' cps_e)      $
       counterexample ("cps_eval_e = " ++ pp' cps_eval_e) $
       counterexample ("eval_cps_e = " ++ pp' eval_cps_e) $
       eval_cps_e == cps_eval_e

------------------------------------------------------------------------------
-- what about small-step evaluation?

-- | __Simulation__ : CPS preserves small-step evaluation
--
--     if    e -> e'
--     then  cps e -> cps e'
--                   
-- NB: not true, due to administrative redexes     
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
            Nothing -> discard -- if e does not step, ignore this test
            Just v -> v
     cps_e' = cps e'

-- | __Simulation__ : CPS preserves small-step evaluation
--
--     if    e -> e'
--     then  cps e ->* cps e'
--      
-- NB: not true, not even for PureLC                  
prop_cps_steps :: Tm Z -> Property
prop_cps_steps e =
     counterexample ("e      = " ++ pp e) $
     counterexample ("e'     = " ++ pp e') $
     counterexample ("cps_e  = " ++ pp' cps_e) $
     counterexample ("cps_e' = " ++ pp' cps_e') $
     step_star vv cps_e cps_e'
  where
     e' = case step e of
            Nothing -> discard -- if e does not step, ignore this test
            Just v -> v
     cps_e  = cpsK e
     cps_e' = cpsK e'
     vv  = ("k" ::: VNil)
     pp' = ppWith ("k" ::: VNil)

     
-- | does e ->* e' hold?     
step_star :: Vec n String -> Tm n -> Tm n -> Property
step_star vv e e' = 
    counterexample ("steps to  => " ++ ppWith vv e) $
    e == e' .||. case step e of
                    Nothing -> property False  -- e should not get stuck
                    Just e1 -> step_star vv e1 e'

------------------------------------------------------------------------
-- * Optimized CPS translation
------------------------------------------------------------------------

-- We can define a better translation that does not introduce "administrative" 
-- reductions into the output. To do so, we need to generalize the continuation
-- argument to the translation.

-- | A "continuation" in scope @n@
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
-- * Optimized CPS translation (One-pass meta/obj continuations)
------------------------------------------------------------------------
   
-- | entry point with identity function
cpsOpt :: Tm Z -> Tm Z
cpsOpt e = cpsExpOpt zeroE e (Obj idTm)

-- | entry point with free variable "k"
cpsOptK :: Tm Z -> Tm (S Z)
cpsOptK e = cpsExpOpt zeroE e (Obj (Var FZ))


cpsExpOpt :: forall n m. Env Tm n m -> Tm n -> Cont m -> Tm m
cpsExpOpt r (Var x) k = applyCont k (applyEnv r x)
cpsExpOpt r Unit k    = applyCont k Unit
cpsExpOpt r (Lam b) k = applyCont k $ 
    Lam (bind1 (getLocalName b) 
      (Lam (bind1 (LocalName "k")
          (cpsExpOpt (skip (up r)) (getBody b) (Obj (Var FZ))))))
cpsExpOpt r (Pair t1 t2) k =
    cpsExpOpt r t1 (Meta (bind1 (LocalName "v")
       (cpsExpOpt r' t2 (Meta (bind1 (LocalName "w")
          (applyCont k'' (Pair (Var (FS FZ)) (Var FZ))))))))
      where 
        r' :: Env Tm n (S m)
        r'  = r .>> wk
        k'' :: Cont (S (S m))
        k'' = applyE (wk .>> wk) k
cpsExpOpt r (App t1 t2) k = 
    cpsExpOpt r t1 (Meta (bind1 (LocalName "v")
      (cpsExpOpt r' t2 (Meta (bind1 (LocalName "w")
          (App (App (Var (FS FZ)) (Var FZ)) (reifyCont k'')))))))  
       where
         r'  = r .>> wk
         k'' = applyE (wk .>> wk) k
cpsExpOpt r (Inj i e) k =
    cpsExpOpt r e (Meta (bind1 (LocalName "v")
       (applyCont k' (Inj i (Var FZ)))))
       where k' = applyE wk k
-- [[case e of { pᵢ -> bᵢ }]] k = [[e]] (λz. case z of { pᵢ -> [[bᵢ]] k' })
cpsExpOpt r (Match e brs) k =
    cpsExpOpt r e (Meta (bind1 (LocalName "z") (Match (Var FZ) (map cpsBranch brs))))
    where
        r' = r .>> wk
        k' = applyE wk k
        cpsBranch :: Branch n -> Branch (S m)
        cpsBranch (Branch b) =
            let pat   = Pat.getPat b
                sz    = size pat
                body' = cpsExpOpt (upN sz r') (Pat.getBody b) (applyE @Tm (shiftNE sz) k')
            in Branch (Pat.bind pat body')
    
------------------------------------------------------------------------
-- * Properties of Optimized CPS translation
------------------------------------------------------------------------
  


-- | __Correctness__: CPS opt preserves big-step evaluation
--
-- @eval(e) == eval(cps(e))@ for firstorder values
prop_cpsOpt_result_firstorder :: Property
prop_cpsOpt_result_firstorder = forAll0 Typed Full $ \e ->
    let
       cps_e = cpsOpt e
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

-- | __Correctness__: CPS opt preserves big-step evaluation
--
-- @eval(e) == eval(cps(e))@ with continuation parameter
prop_cpsOpt_eval_simulates_open :: Property
prop_cpsOpt_eval_simulates_open = forAll0 Typed Full $ \e ->
       counterexample ("e          = " ++ pp e)          $
       counterexample ("cps_e      = " ++ pp (cps e))    $
       reduce (cpsOptK e) == (cpsOptK <$> reduce e)   -- lift cps over Maybe type

-- | __Simulation__ : CPS preserves small-step evaluation
--
--     if    e -> e'
--     then  cpsOpt e ->* cpsOpt e'
--      
-- NB: not true for full language             
prop_cpsOpt_steps :: Property
prop_cpsOpt_steps = forAll0 Typed PureLC $ \ e ->
  let 
     e' = case step e of
            Nothing -> discard -- if e does not step, ignore this test
            Just v -> v
     cps_e  = cpsOptK e
     cps_e' = cpsOptK e'
     vv  = ("k" ::: VNil)
     pp' = ppWith ("k" ::: VNil)
   in
     counterexample ("e      = " ++ pp e) $
     counterexample ("e'     = " ++ pp e') $
     counterexample ("cps_e  = " ++ pp' cps_e) $
     counterexample ("cps_e' = " ++ pp' cps_e') $
     step_star vv cps_e cps_e'

------------------------------------------------------------------------
-- * Run all properties
------------------------------------------------------------------------

-- | Run all QuickCheck properties in this module.
-- Properties marked NB are known to be false and are expected to fail.
testAll :: IO ()
testAll = do
    let args = stdArgs { maxSuccess = 1000 }
    -- Naive CPS
    putStrLn "=== Naive CPS ==="
    putStrLn "prop_cps_result (NB: expected to fail):"
    quickCheckWith args prop_cps_result
    putStrLn "prop_cps_result_firstorder:"
    quickCheckWith args prop_cps_result_firstorder
    putStrLn "prop_cps_eval_cps (NB: expected to fail):"
    quickCheckWith args prop_cps_eval_cps
    putStrLn "prop_cps_reduce_cps (NB: expected to fail for pattern matching):"
    quickCheckWith args prop_cps_reduce_cps
    putStrLn "prop_cps_reduce_cps_pure:"
    quickCheckWith args prop_cps_reduce_cps_pure
    putStrLn "prop_cps_step (NB: expected to fail):"
    quickCheckWith args prop_cps_step
    putStrLn "prop_cps_steps (NB: expected to fail):"
    quickCheckWith args prop_cps_steps
    -- Optimized CPS
    putStrLn "=== Optimized CPS ==="
    putStrLn "prop_cpsOpt_result_firstorder:"
    quickCheckWith args prop_cpsOpt_result_firstorder
    putStrLn "prop_cpsOpt_eval_simulates_open:"
    quickCheckWith args prop_cpsOpt_eval_simulates_open
    putStrLn "prop_cpsOpt_steps:"
    quickCheckWith args prop_cpsOpt_steps
