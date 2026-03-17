module Tutorial.Exercise3 where

import Tutorial.Top
import Data.Vec 


------------------------------------------------------------------------
-- * Exercise 1: The colon variant of CPS translation
------------------------------------------------------------------------

-- V[[ t ]]    value translation
-- ( t : k )   colon translation

-- V[[x]] = x
-- V[[()]] = ()
-- V[[\x.e]] = \x k. E[[e]]k 

-- The key idea is that if a 

-- E[[ v ]]k = k v
-- E[[ (v1,e1) ]]k = 
-- E[[ (e1,e2) ]]k = 

cpsVal :: Env Tm m1 m2 -> Tm m1 -> Tm m2
cpsVal r (Var x) = applyEnv r x
cpsVal r Unit    = Unit
cpsVal r (Lam b) =  
    (Lam (bind1 (getLocalName b) 
      (Lam (bind1 (LocalName "k")
          (cpsExp (skip (up r)) (getBody b) (Var FZ))))))
cpsVal r (Pair v1 v2) = 
    Pair (cpsVal r v1) (cpsVal r v2)
cpsVal r (Inj i v1) = 
    Inj i (cpsVal r v1)
cpsVal r _ = error "Not a value"

colon :: Env Tm n1 n2 -> Tm n1 -> Tm n2 -> Tm n2
colon r v k | isVal v = App k (cpsVal r v)
-- new cases, when subterms are values
colon r (App v1 v2) k | isVal v1 && isVal v2 = 
    App (App (cpsVal r v1) (cpsVal r v2)) k
colon r (App v1 e2) k | isVal v1 = 
    colon r e2 (Lam (bind1 (LocalName "w")
                  (App (App v1' (Var FZ)) k')))
    where v1' = applyE wk (cpsVal r v1)
          k'  = applyE wk k
-- standard translation, when e1 and e2 are not values
colon r (App e1 e2) k = 
    colon r e1 (Lam (bind1 (LocalName "v")
                 (colon r' e2
                     (Lam (bind1 (LocalName "w")
                        (App (App (Var (FS FZ)) (Var FZ)) k'))))))
    where 
        r' = r .>> wk
        k' = applyE (wk .>> wk) k
{- SOLN -}
colon r (Pair v1 e2) k | isVal v1 = 
    colon r e2 (Lam (bind1 (LocalName "w")
                  (App k' (Pair v1' (Var FZ)))))
    where v1' = applyE wk (cpsVal r v1)
          k'  = applyE wk k
{- STUBWITH -- TODO: add a case for Pair, when e1 is a value -}
-- standard translation, when e1 and e2 are not values
colon r (Pair e1 e2) k = 
    colon r e1 (Lam (bind1 (LocalName "v")
                 (cpsExp r' e2
                     (Lam (bind1 (LocalName "w")
                        (App k' (Pair (Var (FS FZ)) (Var FZ))))))))
    where 
        r' = r .>> wk
        k' = applyE (wk .>> wk) k
-- standard translation: e1 is not a value
colon r (Inj i e1) k =
    colon r e1 (Lam (bind1 (LocalName "w")
                  (App k' (Inj i (Var FZ)))))
    where k'  = applyE wk k
{- SOLN -}
colon r (MatchUnit v1 e2) k | isVal v1 = 
    MatchUnit (cpsVal r v1) (colon r e2 k)
{- STUBWITH -- TODO: add a case for MatchUnit when e1 is a value -}
-- standard translation: e1 is not a value
colon r (MatchUnit e1 e2) k = 
    colon r e1 (Lam (bind1 (LocalName "v1")
                    (MatchUnit (Var FZ) (colon r' e2 k'))))
    where r' = r .>> wk
          k' = applyE wk k
{- SOLN -}
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
{- STUBWITH -- TODO: add a case for MatchPair when e1 is a value -}
colon r (MatchPair e1 b) k = 
    colon r e1 (Lam (bind1 (LocalName "v1")
      (MatchPair (Var FZ) (bind2 x1 x2 
        (colon (up (up (r .>> wk))) (getBody2 b) k'''))))) 
        where
            names = getLocalName2 b
            x1 = names ! FZ
            x2 = names ! FS FZ
            k''' = applyE (wk .>> wk .>> wk) k
{- SOLN -}
colon r (MatchSum v1 e1 e2) k | isVal v1 = 
    (MatchSum (cpsVal r v1)
           (bind1 (getLocalName e1)
                  (colon (up r) (getBody e1) k'))
           (bind1 (getLocalName e2)
                  (colon (up r) (getBody e2) k')))
    where k' = applyE wk k
{- STUBWITH -- TODO: add a case for MatchSUm when e0 is a value -}
colon r (MatchSum e0 e1 e2) k = 
    cpsExp r e0 (Lam (bind1 (LocalName "v1")
       (MatchSum (Var FZ)
           (bind1 (getLocalName e1)
                  (colon (up (skip r)) (getBody e1) k''))
           (bind1 (getLocalName e2)
                  (colon (up (skip r)) (getBody e2) k'')))))
    where k'' = applyE (wk .>> wk) k
colon r _ _ = error "Impossible"
----------------------------------------------------------------------------

-- The standard CPS translation steps to the colon translation
--  [[e]]k ->* (e : k) 
-- NOT true
prop_a :: Property
prop_a = forAll genTypedPureLC $ \ e ->
            step_star ("k" ::: VNil) 
              (cpsExp zeroE e (Var FZ)) (colon zeroE e (Var FZ))


-- | The colon translation simulates the step relation
-- | If e -> e' then (e : k) ->* (e' : k)
-- NB: not true
prop_simulation :: Property
prop_simulation = forAll genTypedPureLC $ \ e ->
   let
       cps_e = colon zeroE e k
       cps_e' = colon zeroE e' k
       k = Var FZ
       vv = "k" ::: VNil
       e' = case step e of 
            Left _ -> discard
            Right e1 -> e1
    in 
        step_star vv cps_e cps_e'

-- | If  e ->* v then  [[e]]k ->* [[v]]k
prop_plotkin :: Property
prop_plotkin = forAll genTypedPureLC $ \e ->
    let
       cps_e = cpsExp zeroE e k
       cps_v = cpsExp zeroE v k
       k = Var FZ
       vv = "k" ::: VNil
       v = case eval e of 
            Nothing -> discard
            Just v1 -> v1
    in
      step_star vv cps_e cps_v  