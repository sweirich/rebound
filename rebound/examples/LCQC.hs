-- |
-- Module      : LCQC
-- Description : Generators for well-scoped lambda calculus terms
-- Stability   : experimental
--
-- This module demonstrates the use of well-scoped lambda calculus terms 
-- with QuickCheck. It then demonstrates how to use QC to test the normalization
-- functions in the `LC` module.
module LCQC where

import LC
import Test.QuickCheck
import Rebound
import Rebound.Bind.Single 
import Data.Fin
import Data.Maybe as Maybe

----------------------------------------------
-- Generating well-scoped expressions
----------------------------------------------

-- | Generate an expression in scope `n`, using 
-- size parameter sz
-- >>> sample' (genExp s3 10) 
-- [1,(1 2),2,((λ. 1) 2),(2 (λ. 2)),(((λ. 0) 1) 1),((λ. 2) 2),(λ. ((2 1) (3 1))),(1 ((0 0) (0 0))),(λ. ((2 3) 0)),(((1 2) (1 2)) (λ. (0 3)))]
genExp :: forall n. SNat n -> Int -> Gen (Exp n)
genExp n sz = 
    let 
        genLam = Lam <$> (bind <$> genExp (next n) (sz `div` 2))
        genApp = App <$> genExp n (sz `div` 2) <*> genExp n (sz `div` 2)
    in
    case snat_ n of 
       SZ_ -> if sz <= 1 
                then pure $ Lam (bind (Var 0))  -- smallest closed term
                else oneof [genLam, genApp]     -- closed term, no vars
       SS_ x -> 
         let 
            genVar = withSNat x $ elements $ map Var universe
         in 
            if sz <= 1 
              then genVar
              else oneof [genVar, genLam, genApp]

-- | shrink a lambda calculus term, maintaining the same scope.
shrinkExp :: SNatI n => Exp n -> [Exp n]
shrinkExp (Var FZ) = [] 
shrinkExp (Var x ) = [ Var (pred x) ]
shrinkExp (Lam t)  = [ Lam (bind t') | t' <- shrinkExp (getBody t) ]
shrinkExp (App f a) = 
  [f,a] ++ [ App f' a | f' <- shrinkExp f]   
        ++ [ App f a' | a' <- shrinkExp a]

-- | arbitrary instance for lambda calculus terms
instance SNatI n => Arbitrary (Exp n) where
  arbitrary :: SNatI n => Gen (Exp n)
  arbitrary = sized (genExp snat)
  shrink :: SNatI n => Exp n -> [Exp n]
  shrink = shrinkExp


----------------------------------------------
-- Property-based testing example
----------------------------------------------

{-

Let's use QuickCheck to make sure that our various
normalization functions for the lambda calculus all produce the 
same result.

However, we need to deal with the fact that not all lambda 
calculus terms normalize. Therefore, we will instruct QC to discard
the test case if the expression does not normalize within 0.1 seconds.
We will also discard expressions that are already in normal form.
-}

prop_normalize :: (Exp n -> Exp n) -> Exp n -> Property
prop_normalize f e = discardAfter 100000 $
    e /= e' ==> e' == f e
   where e' = nf e 

prop_nf1 :: Exp Z -> Property
prop_nf1 = prop_normalize nf1 

prop_nfEnv :: Exp Z -> Property
prop_nfEnv = prop_normalize nfEnv
