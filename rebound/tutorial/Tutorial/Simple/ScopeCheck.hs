{-|
Module      : Simple.ScopeCheck
Description : Conversion to and from Named representation
Copyright   : (c) Stephanie Weirich, 2026
License     : MIT
Maintainer  : sweirich@seas.upenn.edu
Stability   : experimental

A module to display named syntax terms nicely. 

This pretty printer is built using the `Prettyprinter` 
library, which includes a number of definitions for 
turning data into `Doc`

-}
module Tutorial.Simple.ScopeCheck where

import Test.QuickCheck

import Data.Fin
import Data.SNat
import qualified Rebound as Rebound
import Rebound.Bind.PatN as Rebound hiding (Ctx)

import qualified Tutorial.Named.Syntax as N
import qualified Tutorial.Named.PP as N
import qualified Tutorial.Named.Parser as N
import qualified Tutorial.Simple.Syntax as I
import Tutorial.Simple.Gen
import Tutorial.Lib 


instance Injection I.Ty N.Ty where
    inject (t1 I.:-> t2) = inject t1 N.:-> inject t2
    inject I.One = N.unitTy
    inject I.Zero = N.voidTy
    inject (t1 I.:* t2) = N.Prod [inject t1, inject t2]
    inject (t1 I.:+ t2) = N.Sum [inject t1, inject t2]

instance Projection N.Ty I.Ty where
   project (t1 N.:-> t2) = (I.:->) <$> project t1 <*> project t2
   project (N.Prod []) = pure I.One
   project (N.Prod [t1,t2]) = (I.:*) <$> project t1 <*> project t2
   project (N.Prod _) = Nothing
   project (N.Sum []) = pure I.Zero
   project (N.Sum [t1,t2]) = (I.:+) <$> project t1 <*> project t2
   project (N.Sum _) = Nothing 
   
type Ctx n = Fin n -> String

-- | the empty context has an empty domain
emptyCtx :: Ctx Z
emptyCtx = \x -> case x of {}

-- | extend a context with a new type, enlarging its domain
(+%) :: Ctx n -> String -> Ctx (S n)
(+%) g a = \x -> case x of { FZ -> a ; FS y -> g y }


vname :: SNat n -> String
vname n = "x" ++ show (toInt n)

-- | Convert a named expression to deBruijn indices, checking to make
-- sure that the expression is well scoped
instance Injection (I.Tm Z) N.Tm where
    inject = to (\f -> case f of {}) where
        to :: forall n. SNatI n => (Fin n -> String) -> I.Tm n -> N.Tm 
        to vs (I.Var x) = N.Var (vs x)
        to vs (I.Lam t) = N.Lam s (to (vs +% s) (Rebound.getBody1 t)) 
                             where s = vname (snat @n)
        to vs (I.App e1 e2)= N.App (to vs e1) (to vs e2)
        to vs (I.Unit) = N.Pair []
        to vs (I.Pair e1 e2) = N.Pair [to vs e1, to vs e2]
        to vs (I.Inj i e) = N.Inj i (to vs e)
        to vs (I.MatchUnit e1 e2) = N.Case (to vs e1) [(N.unitTm, to vs e2)]
        to vs (I.MatchPair e1 e2) = N.Case (to vs e1) [(N.Pair[N.Var s1, N.Var s2], to vs' e2')] 
            where s1 = vname (snat @(S n))
                  s2 = vname (snat @n)
                  e2' = Rebound.getBody2 e2
                  vs' = (vs +% s1) +% s2
        to vs (I.MatchSum e e1 e2) = N.Case (to vs e) 
           [ (N.Inj 0 (N.Var s), to (vs +% s) (Rebound.getBody1 e1)),
             (N.Inj 1 (N.Var s), to (vs +% s) (Rebound.getBody1 e2)) ] where 
                    s = vname (snat @n)
        to vs (I.Ann e ty) = N.Ann (to vs e) (inject ty)
        

instance Projection N.Tm (I.Tm Z) where
    project = to [] where
        to :: [(String, Fin n)] -> N.Tm -> Maybe (I.Tm n)
        to vs (N.Var v) = do
            x <- lookup v vs
            return $ I.Var x
        to vs (N.Lam v b) = do
            b' <- to ((v, FZ) : map (fmap FS) vs) b
            return $ I.Lam (Rebound.bind1 b')
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
            return (I.MatchPair a' (Rebound.bind2 b'))
        to vs (N.Case e [(N.Inj 0 (N.Var v1), e1), (N.Inj 1 (N.Var v2), e2)]) = do
            a' <- to vs e
            b1' <- to ((v1, FZ) : map (fmap FS) vs) e1
            b2' <- to ((v2, FZ) : map (fmap FS) vs) e2
            return (I.MatchSum a' (Rebound.bind1 b1') (Rebound.bind1 b2'))
        to vs _ = Nothing


prop_project_round_trip :: I.Tm Z -> Bool
prop_project_round_trip i = project ((inject i) :: N.Tm) == Just i

prop_parse_round_trip :: I.Tm Z -> Bool
prop_parse_round_trip i = N.parseTm (show (N.test (inject i :: N.Tm))) == Right (inject i) 
