-- |
-- Module      : ScopeCheck
-- Description : Scope checking the Untyped lambda calculus
-- Stability   : experimental
--
-- This module demonstrates a translation from unscoped to well-scoped terms

module PiForall.ScopeCheck where

import Rebound.Bind.Pat (PatList(..))
import qualified Rebound.Bind.Pat as Pat
import Rebound.Bind.Scoped ((<:>))
import qualified Rebound.Bind.Scoped as Scoped
import qualified Rebound.Bind.Local as L
import Data.Maybe (fromJust)
import qualified PiForall.ConcreteSyntax as C
import qualified PiForall.Syntax as S
import Rebound.Lib
             

push :: a -> [(a, Fin n)] -> [(a, Fin (S n))]
push x vs = (x, FZ) : map (fmap FS) vs

data ScopedPattern n = forall p. SNatI p =>
   ScopedPattern (S.Pattern p) [(LocalName, Fin (p + n))]

data ScopedPatList n = forall p. SNatI p =>
   ScopedPatList (Pat.PatList S.Pattern p) [(LocalName, Fin (p + n))]

scopeCheckModule :: C.Module -> Maybe S.Module
scopeCheckModule m = do 
  entries <- mapM scopeCheckEntry (C.moduleEntries m)
  return $ S.Module {
              S.moduleName = C.moduleName m,
              S.moduleImports = C.moduleImports m,
              S.moduleEntries = entries,
              S.moduleConstructors = C.moduleConstructors m
            }

scopeCheckEntry :: C.ModuleEntry -> Maybe S.ModuleEntry
scopeCheckEntry (C.ModuleDecl gn ty) = S.ModuleDecl gn <$> scopeCheck ty
scopeCheckEntry (C.ModuleDef gn tm) = S.ModuleDef gn <$> scopeCheck tm
scopeCheckEntry (C.ModuleData dn datadef) = S.ModuleData dn <$> scopeCheckData datadef

data ScopedTele n = 
  forall p. SNatI p => ScopedTele [(LocalName, Fin (p + n))] (S.Telescope p n) 

scopeCheckData :: C.DataDef -> Maybe S.DataDef
scopeCheckData (C.DataDef delta s cs) = do 
  ScopedTele scope (delta' :: S.Telescope n Z) <- scopeCheckTele [] delta
  case axiomPlusZ @n of 
    Refl -> S.DataDef delta' <$> scopeCheck s <*> mapM (scopeCheckConstructor scope) cs

scopeCheckTele :: forall n. SNatI n => [(LocalName, Fin n)] -> C.Telescope -> Maybe (ScopedTele n)
scopeCheckTele scope [] = Just $ ScopedTele scope Scoped.TNil
scopeCheckTele scope (C.EntryDecl n ty : entries) = do 
  ty' <- to scope ty 
  let scope' :: [(LocalName, Fin (S n))]
      scope' = push n scope
  ScopedTele (ss    :: [(LocalName, Fin (p + 'S n))]) 
             (tele' :: S.Telescope p (S n)) <- scopeCheckTele scope' entries
  let fact :: p + S n :~: (p + N1) + n
      fact = axiomAssoc @p @N1 @n
  withSNat (sPlus (snat @p) s1) $ case fact of { Refl -> do
    let ret = S.LocalDecl n ty' <:> tele'
    return $ ScopedTele ss ret }
scopeCheckTele scope (C.EntryDef n tm : entries) = do
  tm' <- to scope tm
  ScopedTele ss (tele' :: S.Telescope p n) <- scopeCheckTele scope entries
  case axiomPlusZ @p of 
    Refl -> do
      ln <- lookup n scope
      let ret = S.LocalDef ln tm' <:> tele'
      return $ ScopedTele ss ret

scopeCheckConstructor :: SNatI n => [(LocalName, Fin n)] -> C.ConstructorDef 
  -> Maybe (S.ConstructorDef n)
scopeCheckConstructor scope (C.ConstructorDef p dc theta) = do
  ScopedTele _ theta' <- scopeCheckTele scope theta
  pure $ S.ConstructorDef dc theta'

-- | Convert a named expression to deBruijn indicies, checking to make
-- sure that the expression is well scoped
scopeCheck :: C.Term -> Maybe (S.Term Z)
scopeCheck = to []
  
toM :: forall n. SNatI n => [(LocalName, Fin n)] -> C.Match ->
  Maybe (S.Match n)
toM vs (C.Branch pat tm) = do 
  ScopedPattern (pat' :: S.Pattern p) vs' <- toP vs pat
  tm' <- withSNat (sPlus (snat :: SNat p) (snat :: SNat n)) $ to vs' tm
  return (S.Branch (Pat.bind pat' tm'))

toP :: SNatI n => [(LocalName, Fin n)] -> 
  C.Pattern -> Maybe (ScopedPattern n)
toP vs (C.PatVar x) = 
  return (ScopedPattern (S.PatVar x) ((x, FZ): map (fmap FS) vs))
toP vs (C.PatCon n pats) = do
  ScopedPatList pats' vs' <- toPL vs pats
  return (ScopedPattern (S.PatCon n pats') vs')

toPL :: forall n. SNatI n => [(LocalName, Fin n)] -> 
  [C.Pattern] -> Maybe (ScopedPatList n)
toPL vs [] = return $ ScopedPatList Pat.PNil vs
toPL vs (p :ps) = do
  ScopedPattern (p'  :: S.Pattern p) vs' <- toP vs p
  withSNat (sPlus (snat :: SNat p) (snat :: SNat n)) $ do
      ScopedPatList (ps' :: Pat.PatList S.Pattern p1) vs'' <- 
    
          toPL vs' ps
      Refl <- Just (axiomAssoc @p1 @p @n)
      withSNat (sPlus (snat :: SNat p1) (snat :: SNat p)) (return $ ScopedPatList (Pat.PCons p' ps') vs'')

to :: SNatI n => [(LocalName, Fin n)] -> C.Term -> Maybe (S.Term n)
to vs C.TyType = return S.TyType
to vs (C.Var v) = case lookup v vs of
                    Just x -> Just $ S.Var x
                    Nothing -> Just $ S.Global y where LocalName y = v
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
to vs (C.TyEq a b) = do
  a' <- to vs a
  b' <- to vs b
  return $ S.TyEq a' b'
to vs C.TmRefl = return S.TmRefl
to vs (C.Subst a b) = do
  a' <- to vs a
  b' <- to vs b
  return $ S.Subst a' b'
to vs (C.Contra a) = do
  a' <- to vs a
  return $ S.Contra a'
to vs C.TrustMe = return S.TrustMe
to vs C.PrintMe = return S.PrintMe
