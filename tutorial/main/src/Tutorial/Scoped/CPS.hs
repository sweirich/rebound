{-|
Module      : Tutorial.Scoped.CPS
Description : Call-by-value CPS translation for the simply-typed lambda calculus

This module implements a call-by-value CPS translation.  


Why is the CPS translation important?
 - Makes the evaluation order explicit
 - Useful for programmers (compilation / cooperative concurrency)
 - Fascinating connection with classical logic 

Plotkin's translation is defined by the following equations, where @[[e]] k@ means
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


Why cover it today?

Example of a translation that requires *renaming* variables during traversal.




-}
module Tutorial.Scoped.CPS where

import Test.QuickCheck
import Tutorial.Scoped.Syntax
import qualified Rebound.Bind.Pat as Pat
import Data.Vec ( (!) )
import Data.Maybe as Maybe
import Tutorial.Scoped.Gen
import Tutorial.Scoped.Eval
import Tutorial.Scoped.ScopeCheck


------------------------------------------------------------------------
-- * Top-level entry point 
------------------------------------------------------------------------


-- | Identity function  "\x.x"
idTm :: Tm Z
idTm = Lam (bind (LocalName "x") (Var FZ))


-- | Apply the CPS translation to a closed term, using the identity
-- continuation @λx. x@ so that the result is still a closed term.
cps :: Tm Z -> Tm Z
cps e = cpsExp zeroE e idTm


-- Example:
--   [[ \x.x ]] k == k (\x.\k'. k' x)
--   [[ \.0  ]] k == k (\ \ . 0 1)      <- x was 0 before, is now 1

-- >>> pp (cps idTm)


------------------------------------------------------------------------
-- * CBV CPS translation 
------------------------------------------------------------------------

wk :: SNat m -> Env Tm n (m + n)
wk = shiftNE

wk1 :: Env Tm n (S n)
wk1 = wk s1

cpsExp :: forall n m. Env Tm n m -> Tm n -> Tm m -> Tm m
-- [[x]] k = k x
cpsExp r (Var x) k = App k (applyEnv r x)
-- [[()]] k = k ()
cpsExp r Unit k    = App k Unit
-- [[λx. e]] k = k (λx. λk'. [[e]] k')
cpsExp r (Lam b) k = 
    App k (Lam (bind (LocalName (name (getPat b))) 
            (Lam (bind (LocalName "k") (cpsExp r' (getBody b) k')))))
       where r' :: Env Tm (S n) (S (S m))
             r' = up r .>> wk1
             k' :: Tm (S (S m))
             k' = Var FZ
-- [[e1 e2]] k = [[e1]] (λx. [[e2]] (λy. x y k))
cpsExp r (App e1 e2) k = 
    cpsExp r e1 (Lam (bind (LocalName "x") 
                       (cpsExp (r .>> wk s1) e2 (Lam (bind (LocalName "y")
                            (App (App (Var (FS FZ)) (Var FZ)) k'))))))
        where k' :: Tm (S (S m))
              k' = applyE (wk s2) k

-- [[(e1, e2)]] k = [[e1]] (λx. [[e2]] (λy. k (x,y)))
cpsExp r (Pair t1 t2) k =
    cpsExp r t1 (Lam (bind (LocalName "v")
       (cpsExp (skip r) t2 (Lam (bind (LocalName "w")
          (App k'' (Pair (Var (FS FZ)) (Var FZ))))))))
      where 
        r'  = r .>> wk s1
        k'' = applyE (wk s2) k
-- [[inj i e]] k = [[e]]  (λx. k (inj i x))
cpsExp r (Inj i e) k =
    cpsExp r e (Lam (bind (LocalName "v")
       (App k' (Inj i (Var FZ)))))
       where k' = applyE (wk s1) k
-- [[case e of { pᵢ -> bᵢ }]] k = [[e]] (λz. case z of { pᵢ -> [[bᵢ]] k' })
cpsExp r (Match e brs) k =
    cpsExp r e (Lam (bind (LocalName "z") (Match (Var FZ) (map cpsBranch brs))))
    where
        r' = r .>> wk s1
        k' = applyE (wk s1) k
        cpsBranch :: Branch n -> Branch (S m)
        cpsBranch (Branch b) =
            let pat   = Pat.getPat b
                sz    = size pat
                body' = cpsExp (upN sz r') (Pat.getBody b) (applyE (wk sz) k')
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
-- NB: this property fails, why?
prop_cps_result :: Property
prop_cps_result = forAll0 Scoped Full $ \ e ->
      let cps_e      = cps e
          eval_e     = fromMaybe discard $ eval e 
          eval_cps_e = fromMaybe discard $ eval (cps_e)
       in
         counterexample ("*** cps_e =\n" ++ pp cps_e) $
         counterexample ("*** eval_e =\n" ++ pp eval_e) $
         counterexample ("*** eval_cps_e =\n" ++ pp eval_cps_e) $
         discardAfter 10000 $
         eval_e == eval_cps_e

-- | CPS preserves big-step evaluation for *firstorder* values
--
-- @eval(e) == eval(cps(e))@ for firstorder values
-- 
prop_cps_result_firstorder :: Property
prop_cps_result_firstorder = forAll0 Scoped Full $ \e ->
    let
       cps_e      = cps e
       eval_e     = fromMaybe discard $ eval e 
       eval_cps_e = fromMaybe discard $ eval cps_e 
    in
      counterexample ("e          = " ++ pp e)          $
      counterexample ("eval_e     = " ++ pp eval_e)     $
      counterexample ("cps_e      = " ++ pp cps_e)      $
      counterexample ("eval_cps_e = " ++ pp eval_cps_e) $
      discardAfter 10000 $
      isFirstOrder eval_e ==>
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
-- property that we might want to hold
-- 
--     if      e  =>  v 
--                 
--     then    cps e => cps v
--
--   we can write this property succinctly as:
--      eval (cps e) = cps (eval e) 
--
-- NB: this property fails, why?
prop_cps_simulates :: Property
prop_cps_simulates = forAll0 Scoped Full $ \e ->
       let eval_cps_e = fromMaybe discard $ eval (cps e)
           cps_eval_e = fromMaybe discard $ cps <$> eval e
        in
           counterexample ("*** cps_e =\n" ++ pp (cps e))    $
           counterexample ("*** eval_cps_e =\n" ++ pp eval_cps_e) $
           counterexample ("*** cps_eval_e =\n" ++ pp cps_eval_e) $
           discardAfter 10000 $
           eval_cps_e == cps_eval_e

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
  Meta  :: Bind1 n -> Cont n
    

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
    applyE r (Obj o) = Obj (applyE r o)
    applyE r (Meta k) = Meta (applyE r k)

------------------------------------------------------------------------
-- * Optimized CPS translation (One-pass meta/obj continuations)
------------------------------------------------------------------------
   
-- | entry point with identity function
cpsOptId :: Tm Z -> Tm Z
cpsOptId e = cpsExpOpt zeroE e (Obj idTm)

-- | entry point with meta-identity function
cpsOpt :: Tm Z -> Tm Z
cpsOpt e = cpsExpOpt zeroE e (Meta (bind (LocalName "x") (Var FZ)))


-- | optimized CPS translation
cpsExpOpt :: forall n m. Env Tm n m -> Tm n -> Cont m -> Tm m
cpsExpOpt r (Var x) k = applyCont k (applyEnv r x)
cpsExpOpt r Unit k    = applyCont k Unit
cpsExpOpt r (Lam b) k = applyCont k $ 
    Lam (bind (getPat b) 
      (Lam (bind (LocalName "k")
          (cpsExpOpt (skip (up r)) (getBody b) (Obj (Var FZ))))))
cpsExpOpt r (Pair t1 t2) k =
    cpsExpOpt r t1 (Meta (bind (LocalName "v")
       (cpsExpOpt r' t2 (Meta (bind (LocalName "w")
          (applyCont k'' (Pair (Var (FS FZ)) (Var FZ))))))))
      where 
        r' :: Env Tm n (S m)
        r'  = r .>> wk s1
        k'' :: Cont (S (S m))
        k'' = applyE (wk s2) k
cpsExpOpt r (App t1 t2) k = 
    cpsExpOpt r t1 (Meta (bind (LocalName "v")
      (cpsExpOpt r' t2 (Meta (bind (LocalName "w")
          (App (App (Var (FS FZ)) (Var FZ)) (reifyCont k'')))))))  
       where
         r'  = r .>> wk s1
         k'' = applyE (wk s2) k
cpsExpOpt r (Inj i e) k =
    cpsExpOpt r e (Meta (bind (LocalName "v")
       (applyCont k' (Inj i (Var FZ)))))
       where k' = applyE (wk s1) k
cpsExpOpt r (Match e brs) k =
    cpsExpOpt r e (Meta (bind (LocalName "z") (Match (Var FZ) (map cpsBranch brs))))
    where
        r' = r .>> wk s1
        k' = applyE (wk s1) k
        cpsBranch :: Branch n -> Branch (S m)
        cpsBranch (Branch b) =
            let pat   = Pat.getPat b
                sz    = size pat
                body' = cpsExpOpt (upN sz r') (Pat.getBody b) (applyE (wk sz) k')
            in Branch (Pat.bind pat body')
    
------------------------------------------------------------------------
-- * Properties of Optimized CPS translation
------------------------------------------------------------------------
  
-- | __Correctness__: CPS opt preserves big-step evaluation
--
-- @eval(e) == eval(cpsOpt(e))@ for firstorder values
-- this also shows that cps e == cpsOpt e for firstorder values
prop_cpsOpt_result_firstorder :: Property
prop_cpsOpt_result_firstorder = forAll0 Typed Full $ \e ->
    let
       cps_e = cpsOpt e
       eval_e = fromMaybe discard $ eval e 
       eval_cps_e = fromMaybe discard $ eval cps_e 
    in
      counterexample ("*** eval_e     =\n" ++ pp eval_e)     $
      counterexample ("*** cps_e      =\n" ++ pp cps_e)      $
      counterexample ("*** eval_cps_e =\n" ++ pp eval_cps_e) $
      discardAfter 10000 $
      isFirstOrder eval_e ==> 
          eval_e == eval_cps_e

-- Do we have
-- @eval(e) == eval(cpsOptId(e))@ 
prop_cpsOptId_simulates :: Property
prop_cpsOptId_simulates = forAll0 Typed Full $ \e ->
   let 
       cps_e = cpsOptId e 
       eval_e = fromMaybe discard $ eval e 
       cps_eval_e = cpsOptId eval_e 
       eval_cps_e = fromMaybe discard $ eval cps_e 
    in
       counterexample ("*** eval_e     =\n" ++ pp eval_e)     $
       counterexample ("*** cps_e      =\n" ++ pp cps_e)      $
       counterexample ("*** cps_eval_e =\n" ++ pp cps_eval_e) $
       counterexample ("*** eval_cps_e  =\n" ++ pp eval_cps_e) $
       eval_cps_e == cps_eval_e

-- | __Correctness__: CPS opt preserves big-step evaluation
--     
--     e => v    iff    cps e => cps v    
-- 
-- @eval(e) == eval(cps(e))@ with meta continuation
prop_cpsOpt_simulates :: Property
prop_cpsOpt_simulates = forAll0 Typed Full $ \e ->
    let 
       cps_e = cpsOpt e 
       eval_e = fromMaybe discard $ eval e 
       cps_eval_e = cpsOpt eval_e 
       eval_cps_e = fromMaybe discard $ eval cps_e 
    in
       counterexample ("*** cps_e      = \n" ++ pp (cps e))    $
       counterexample ("*** cps_eval_e = \n" ++ pp cps_eval_e) $
       counterexample ("*** eval_cps_e = \n" ++ pp eval_cps_e) $
       discardAfter 100000 $
       eval_cps_e == cps_eval_e  


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
    quickCheckWith args prop_cps_simulates
    
    -- Optimized CPS
    putStrLn "=== Optimized CPS ==="
    putStrLn "prop_cpsOpt_result_firstorder:"
    quickCheckWith args prop_cpsOpt_result_firstorder
    

-- pretty printer for terms with a single free variable
pp' :: Tm (S Z) -> String
pp' = ppWith ("k" ::: VNil) -- name for index zero


countApp :: Tm n -> Int
countApp (Var _)        = 0
countApp (Lam b)        = countApp (getBody b)
countApp Unit           = 0
countApp (Pair e1 e2)   = countApp e1 + countApp e2
countApp (Inj _ e)      = countApp e
countApp (App e1 e2)    = 1 + countApp e1 + countApp e2
countApp (Match e brs)  = countApp e + sum (map countAppBranch brs)
  where
    countAppBranch (Branch b) = countApp (getBody b)

countLam :: Tm n -> Int
countLam (Var _)        = 0
countLam (Lam b)        = 1 + countLam (getBody b)
countLam Unit           = 0
countLam (Pair e1 e2)   = countLam e1 + countLam e2
countLam (Inj _ e)      = countLam e
countLam (App e1 e2)    = countLam e1 + countLam e2
countLam (Match e brs)  = countLam e + sum (map countLamBranch brs)
  where
    countLamBranch (Branch b) = countLam (getBody b)

countReturns :: Tm n -> Int
countReturns (Var _) = 0
countReturns Unit = 0 
countReturns (Lam b) = 1 + countReturns (getBody b)
countReturns (Pair e1 e2) = countReturns e1 + countReturns e2
countReturns (Inj _ e) = countReturns e
countReturns (App e1 e2) = countReturns e1 + countReturns e2
countReturns (Match e brs) = length brs + countReturns e + sum (map countReturnsBranch brs)
   where 
     countReturnsBranch (Branch b) = countReturns (getBody b)