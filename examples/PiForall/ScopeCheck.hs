-- |
-- Module      : ScopeCheck
-- Description : Scope checking the Untyped lambda calculus
-- Stability   : experimental
--
-- This module demonstrates a translation from unscoped to well-scoped terms

module PiForall.ScopeCheck where

import qualified AutoEnv.Bind as B
import qualified AutoEnv.Pat.Simple as Pat
import qualified AutoEnv.Pat.LocalBind as L
import Data.Maybe (fromJust)
import qualified PiForall.ConcreteSyntax as C
import qualified PiForall.Syntax as S
import AutoEnv.Lib


data ScopedPattern n = forall p. SNatI p =>
   ScopedPattern (S.Pattern p) 
    [(L.LocalName, Fin (Plus p n))]

data ScopedPatList n = forall p. SNatI p =>
   ScopedPatList (S.PatList p) 
    [(L.LocalName, Fin (Plus p n))]

-- | Convert a named expression to deBruijn indicies, checking to make
-- sure that the expression is well scoped
scopeCheck :: C.Term -> Maybe (S.Term Z)
scopeCheck = to []
  where
    toM :: forall n. SNatI n => [(L.LocalName, Fin n)] -> C.Match ->
      Maybe (S.Match n)
    toM vs (C.Branch pat tm) = do 
      ScopedPattern (pat' :: S.Pattern p) vs' <- toP vs pat
      tm' <- withSNat (sPlus (snat :: SNat p) (snat :: SNat n)) $ to vs' tm
      return (S.Branch (Pat.bind pat' tm'))

    toP :: SNatI n => [(L.LocalName, Fin n)] -> 
      C.Pattern -> Maybe (ScopedPattern n)
    toP vs (C.PatVar x) = 
      return (ScopedPattern (S.PatVar x) ((x, FZ): map (fmap FS) vs))
    toP vs (C.PatCon n pats) = do
      ScopedPatList pats' vs' <- toPL vs pats
      return (ScopedPattern (S.PatCon n pats') vs')

    toPL :: forall n. SNatI n => [(L.LocalName, Fin n)] -> 
      [C.Pattern] -> Maybe (ScopedPatList n)
    toPL vs [] = return $ ScopedPatList S.PNil vs
    toPL vs (p :ps) = do
      ScopedPattern (p'  :: S.Pattern p) vs' <- toP vs p
      withSNat (sPlus (snat :: SNat p) (snat :: SNat n)) $ do
          ScopedPatList (ps' :: S.PatList p1) vs'' <- 
        
             toPL vs' ps
          Refl <- Just (axiomAssoc @p1 @p @n)
          withSNat (sPlus (snat :: SNat p1) (snat :: SNat p)) (return $ ScopedPatList (S.PCons p' ps') vs'')

    to :: SNatI n => [(L.LocalName, Fin n)] -> C.Term -> Maybe (S.Term n)
    to vs C.TyType = return S.TyType
    to vs (C.Var v) = case lookup v vs of
                        Just x -> Just $ S.Var x
                        Nothing -> Just $ S.Global y where L.Box y = v
    to vs (C.Global x) = return (S.Global x)
    to vs (C.Pi a x b) = do
      a' <- to vs a
      b' <- to ((x, FZ) : map (fmap FS) vs) b
      return (S.Pi a' (L.bind x b'))
    to vs (C.Pos s a) = do
      a' <- to vs a 
      return (S.Pos s a')
    to vs (C.Let x a b) = do
      a' <- to vs a
      b' <- to ((x, FZ) : map (fmap FS) vs) b
      return (S.Let a' (L.bind x b'))
    to vs (C.Lam v b) = do
      b' <- to ((v, FZ) : map (fmap FS) vs) b
      return $ S.Lam (L.bind v b')
    to vs (C.App f a) = do
      f' <- to vs f
      a' <- to vs a
      return $ S.App f' a'
    to vs (C.TyCon n tys) = do
      tys' <- mapM (to vs) tys
      return $ S.TyCon n tys'
    to vs (C.DataCon n args) = do
      args' <- mapM (to vs) args
      return $ S.DataCon n args'
    to vs (C.Case a brs) = do
      a' <- to vs a
      brs' <- mapM (toM vs) brs
      return $ S.Case a' brs'
    to vs (C.Ann a b) = do
      a' <- to vs a
      b' <- to vs b
      return $ S.Ann a' b'


