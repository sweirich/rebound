{-|
Module      : Simple.ScopeCheck
Description : Conversion between Scoped and Named representation

-}
module Tutorial.Simple.ScopeCheck where

import Test.QuickCheck

import Data.Fin
import Data.SNat
import Data.Vec ((!))
import qualified Rebound as Rebound


import qualified Tutorial.Named.Syntax as N
import qualified Tutorial.Named.PP as N
import qualified Tutorial.Named.Parser as N
import qualified Tutorial.Simple.Syntax as I
import Tutorial.Simple.Gen
import Tutorial.Lib 


injectTy :: I.Ty -> N.Ty
injectTy = to where 
    to (t1 I.:-> t2) = to t1 N.:-> to t2
    to I.One = N.unitTy
    to I.Zero = N.voidTy
    to (t1 I.:* t2) = N.Prod [to t1, to t2]
    to (t1 I.:+ t2) = N.Sum [to t1, to t2]

-- | Convert from named representation to scoped representation
-- This can fail because the named representation includes n-ary products and sums
projectTy :: N.Ty -> Maybe I.Ty 
projectTy = to where
   to (t1 N.:-> t2) = (I.:->) <$> to t1 <*> to t2
   to (N.Prod []) = pure I.One
   to (N.Prod [t1,t2]) = (I.:*) <$> to t1 <*> to t2
   to (N.Prod _) = Nothing
   to (N.Sum []) = pure I.Zero
   to (N.Sum [t1,t2]) = (I.:+) <$> to t1 <*> to t2
   to (N.Sum _) = Nothing 
   
type Ctx n = Fin n -> String

-- | the empty context has an empty domain
emptyCtx :: Ctx Z
emptyCtx = \x -> case x of {}

-- | extend a context with a new type, enlarging its domain
(+%) :: Ctx n -> String -> Ctx (S n)
(+%) g a = \x -> case x of { FZ -> a ; FS y -> g y }


vname :: SNat n -> String
vname n = "x" ++ show (toInt n)

-- | Convert a variable with debruijn indices to a named term
injectTm :: I.Tm Z -> N.Tm 
injectTm = to emptyCtx where
        to :: forall n. SNatI n => (Fin n -> String) -> I.Tm n -> N.Tm 
        to vs (I.Var x) = N.Var (vs x)
        to vs (I.Lam t) = N.Lam s (to (vs +% s) (I.getBody1 t)) 
                             where s = show (I.getLocalName t)
        to vs (I.App e1 e2)= N.App (to vs e1) (to vs e2)
        to vs (I.Unit) = N.Pair []
        to vs (I.Pair e1 e2) = N.Pair [to vs e1, to vs e2]
        to vs (I.Inj i e) = N.Inj i (to vs e)
        to vs (I.MatchUnit e1 e2) = N.Case (to vs e1) [(N.unitTm, to vs e2)]
        to vs (I.MatchPair e1 e2) = N.Case (to vs e1) [(N.Pair[N.Var s1, N.Var s2], to vs' e2')] 
            where s1 = show (names ! FZ)
                  s2 = show (names ! FS FZ)
                  names = I.getLocalName2 e2
                  e2' = I.getBody2 e2
                  vs' = (vs +% s1) +% s2
        to vs (I.MatchSum e e1 e2) = N.Case (to vs e) 
           [ (N.Inj 0 (N.Var s1), to (vs +% s1) (I.getBody1 e1)),
             (N.Inj 1 (N.Var s2), to (vs +% s2) (I.getBody1 e2)) ] where 
                    s1 = show (I.getLocalName e1)
                    s2 = show (I.getLocalName e2)
        to vs (I.Ann e ty) = N.Ann (to vs e) (injectTy ty)
        

-- Convert a named term to a scoped term
-- Fails if the named term includes free variables
projectTm :: N.Tm -> Maybe (I.Tm Z)
projectTm = to [] where
        to :: [(String, Fin n)] -> N.Tm -> Maybe (I.Tm n)
        to vs (N.Var v) = do
            x <- lookup v vs
            return $ I.Var x
        to vs (N.Lam v b) = do
            b' <- to ((v, FZ) : map (fmap FS) vs) b
            return $ I.Lam (I.bind1 (I.LocalName v) b')
        to vs (N.App f a) = do
            f' <- to vs f
            a' <- to vs a
            return $ I.App f' a'
        to vs (N.Pair []) = return $ I.Unit
        to vs (N.Pair [e1,e2]) = I.Pair <$> to vs e1 <*> to vs e2
        to vs (N.Inj i e1) | i == 0 || i == 1 = I.Inj i <$> to vs e1
        to vs (N.Case e [(N.Pair [], e1)]) = 
            I.MatchUnit <$> to vs e <*> to vs e1
        to vs (N.Case e [(N.Pair [N.Var v1, N.Var v2], e1)]) = do
            a' <- to vs e
            b' <- to ((v2, FZ) : (v1, FS FZ) : map (fmap (FS . FS)) vs) e1
            return (I.MatchPair a' (I.bind2 (I.LocalName v1) (I.LocalName v2) b'))
        to vs (N.Case e [(N.Inj 0 (N.Var v1), e1), (N.Inj 1 (N.Var v2), e2)]) = do
            a' <- to vs e
            b1' <- to ((v1, FZ) : map (fmap FS) vs) e1
            b2' <- to ((v2, FZ) : map (fmap FS) vs) e2
            return (I.MatchSum a' (I.bind1 (I.LocalName v1) b1') (I.bind1 (I.LocalName v2) b2'))
        to vs _ = Nothing


prop_project_round_trip :: I.Tm Z -> Bool
prop_project_round_trip i = projectTm ((injectTm i) :: N.Tm) == Just i

prop_parse_round_trip :: I.Tm Z -> Bool
prop_parse_round_trip i = N.parseTm (show (N.test (injectTm i :: N.Tm))) == Right (injectTm i) 
