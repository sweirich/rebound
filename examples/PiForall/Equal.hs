module PiForall.Equal where

import PiForall.Syntax
import PiForall.Environment (TcMonad, Context )
import qualified PiForall.Environment as Env
import PiForall.PrettyPrint

import AutoEnv.Env as Env
import AutoEnv
import AutoEnv.Pat.Simple as Pat
import AutoEnv.Pat.LocalBind as L
import AutoEnv.Pat.Scoped as Scoped

import Debug.Trace

import Control.Monad(unless, zipWithM, zipWithM_)
import Control.Monad.Except (catchError)

-- | compare two expressions for equality
-- first check if they are alpha equivalent then
-- if not, weak-head normalize and compare
-- throw an error if they cannot be matched up
equate :: forall n. SNatI n => Term n -> Term n -> Scope n -> TcMonad ()
equate t1 t2 s | t1 == t2 = return () 
equate t1 t2 s = do
  n1 <- whnf t1 s 
  n2 <- whnf t2 s
  case (n1, n2) of 
    (TyType, TyType) -> return ()
    (Var x,  Var y) | x == y -> return ()
    (Lam bnd1, Lam bnd2) -> do
      pushScope (L.getLocalName bnd1)  
        (equate @(S n) (L.getBody bnd1) (L.getBody bnd2)) s
    (App a1 a2, App b1 b2) ->
      equate a1 b1 s >> equate a2 b2 s
    (Pi tyA1 bnd1, Pi tyA2 bnd2) -> do 
      equate tyA1 tyA2  s  
      pushScope (L.getLocalName bnd1)                                           
        (equate (L.getBody bnd1) (L.getBody bnd2)) s
      
    (Let rhs1 bnd1, Let rhs2 bnd2) -> do
      equate rhs1 rhs2 s
      pushScope (L.getLocalName bnd1) 
        (equate (L.getBody bnd1) (L.getBody bnd2)) s
    (TyCon c1 ts1, TyCon c2 ts2) | c1 == c2 -> 
      zipWithM_ (\a1 a2 -> equateArgs a1 a2 s) [ts1] [ts2]
    (DataCon d1 a1, DataCon d2 a2) | d1 == d2 -> do
      equateArgs a1 a2 s
    (Case s1 brs1, Case s2 brs2) 
      | length brs1 == length brs2 -> do
      equate s1 s2 s
      -- require branches to be in the same order
      -- on both expressions
      let 
        matchBr :: Match n -> Match n -> Scope n -> TcMonad ()
        matchBr (Branch bnd1) (Branch bnd2) s = 
            Pat.unbind bnd1 $ \p1 a1 -> 
            Pat.unbind bnd2 $ \p2 a2 ->
            case Pat.patEq p1 p2 of
              Just Refl -> 
                pushPatScope p1
                  (equate a1 a2) s
              _ -> Env.err [DS "Cannot match branches in",
                              DD n1, DS "and", DD n2]
      zipWithM_ (\m1 m2 -> matchBr m1 m2 s) brs1 brs2       
    (_,_) -> tyErr n1 n2 s
 where tyErr n1 n2 s = do 
          -- gamma <- Env.getLocalCtx
          -- TODO: use scope in Env.err
          Env.errScope s [DS "Expected", DD n2,
                   DS "but found", DD n1]
               
-- | Match up args
equateArgs :: SNatI n => [Term n] -> [Term n] -> Scope n -> TcMonad ()    
equateArgs (a1:t1s) (a2:t2s) s = do
  equate a1 a2 s
  equateArgs t1s t2s s
equateArgs [] [] s = return ()
equateArgs a1 a2 s = do 
          -- TODO used scope in Env.err
          Env.errScope s [DS "Expected", DD (length a2),
                   DS "but found", DD (length a1) ]
                   


-------------------------------------------------------

-- | Ensure that the given type 'ty' is some tycon applied to 
--  params (or could be normalized to be such)
-- Throws an error if this is not the case 
ensureTCon :: SNatI n => Term n -> Scope n -> TcMonad (TyConName, [Term n])
ensureTCon aty s = do
  nf <- whnf aty s
  case nf of 
    TyCon n params -> return (n, params)    
    _ -> Env.err [DS "Expected a data type but found", DD nf]
    
-------------------------------------------------------
-- | Convert a term to its weak-head normal form.             
-- | TODO: add explicit environment
whnf :: forall n. SNatI n => Term n -> Scope n -> TcMonad (Term n)
whnf (Global y) s = do
  x <- Env.lookupGlobalDef y
  whnf (case axiomPlusZ @n of 
             Refl -> weaken' (snat @n) x) s
     `catchError` \_ -> return (Global y)
  
whnf (Var x) s = do      
  -- maybeDef <- Env.lookupDef x
  -- case maybeDef of 
  --  (Just d) -> whnf d 
  --  _ -> 
          return (Var x)
        
whnf (App t1 t2) s = do
  nf <- whnf t1 s
  case nf of 
    (Lam  bnd) -> do
      whnf (L.instantiate bnd t2) s
    _ -> do
      return (App nf t2)
-- ignore/remove type annotations and source positions when normalizing  
whnf (Ann tm _) s = whnf tm s
whnf (Pos _ tm) s = whnf tm s
whnf (Let rhs bnd) s = do
   whnf (L.instantiate bnd rhs) s
 
whnf (Case scrut mtchs) s = do
  nf <- whnf scrut s      
  case nf of 
    (DataCon d args) -> f mtchs s where
      f (Branch bnd : alts) s = (do
          let pat = Pat.getPat bnd
          ss <- patternMatches nf pat 
          whnf (Pat.instantiate bnd ss) s) 
            `catchError` \ _ -> f alts s
      f [] s = Env.err $ [DS "Internal error: couldn't find a matching",
                    DS "branch for", DD nf, DS "in"] ++ map DD mtchs
    _ -> return (Case nf mtchs){- STUBWITH -}            
-- all other terms are already in WHNF
-- don't do anything special for them
whnf tm s = do
  return tm

-- | 'Unify' the two terms, producing a list of definitions that 
-- must hold for the terms to be equal
-- If the terms are already equal, succeed with an empty list
-- If there is an obvious mismatch, fail with an error
-- If either term is "ambiguous" (i.e. neutral), give up and 
-- succeed with an empty list
unify :: forall n p. SNatI n => SNat p -> Term (Plus p n) -> Term (Plus p n) -> Scope (Plus p n) -> TcMonad [(Fin n, Term n)]
unify p tx ty s = withSNat (sPlus p (snat :: SNat n)) $ do
  (txnf :: Term (Plus p n)) <- whnf tx s
  (tynf :: Term (Plus p n)) <- whnf ty s
  if txnf == tynf
    then return []
    else case (txnf, tynf) of
      (Var x, Var y) | x == y -> return []
      (Var y, yty)  |
        Just (Var y') <- strengthen' p (snat :: SNat n) (Var y),
        Just yty' <- strengthen' p (snat :: SNat n) yty
        -> if not (y' `appearsFree` yty')
            then return [(y', yty')] 
            else return [] 
      (yty, Var y)  |
        Just (Var y') <- strengthen' p (snat :: SNat n) (Var y),
        Just yty' <- strengthen' p (snat :: SNat n) yty
        -> if not (y' `appearsFree` yty')
            then return [(y', yty')] 
            else return [] 
      (DataCon n1 a1, DataCon n2 a2) 
        | n1 == n2 ->  unifyArgs p a1 a2 s
      (TyCon s1 tms1, TyCon s2 tms2)
        | s1 == s2 -> unifyArgs p tms1 tms2 s
      (Lam bnd1, Lam bnd2) -> do
        pushScope (L.getLocalName bnd1) 
          (unify @n (SS p) (L.getBody bnd1) (L.getBody bnd2)) s
      (Pi tyA1 bnd1, Pi tyA2 bnd2) -> do
        ds1 <- unify p tyA1 tyA2 s
        ds2 <- 
          pushScope (L.getLocalName bnd1)
            (unify @n (SS p) (L.getBody bnd1) (L.getBody bnd2)) s
        return (ds1 ++ ds2) 
      _ ->
        if amb txnf || amb tynf
          then return []
          else Env.err [DS "Cannot equate", DD txnf, DS "and", DD tynf] 
  where
    unifyArgs p (t1 : a1s) (t2 : a2s) s = do
      ds <- unify p t1 t2 s
      ds' <- unifyArgs p a1s a2s s
      return $ ds ++ ds'
    unifyArgs p [] [] _ = return []
    unifyArgs _ _ _ _ = Env.err [DS "internal error (unify)"] 


-- | Is a term "ambiguous" when it comes to unification?
-- In general, elimination forms are ambiguous because there are multiple 
-- solutions.
amb :: Term n -> Bool
amb (App t1 t2) = True
amb (Case _ _) = True 
amb _ = False



-- | Determine whether the pattern matches the argument
-- If so return the appropriate substitution
-- otherwise throws an error

-- | Compare a pattern with an expression, potentially
-- producing a substitution for variables
-- bound in the pattern
patternMatches :: forall p n. (SNatI n) => Term n -> Pattern p 
               -> TcMonad (Env Term p n)
patternMatches e (PatVar _) = return (oneE e)
patternMatches (DataCon n args) (PatCon l ps) 
  | l == n = patternMatchList args ps
patternMatches nf pat = Env.err [DS "arg", DD nf, DS "doesn't match pattern", DD pat]

patternMatchList :: forall p n. (SNatI n) => [Term n] -> PatList p -> TcMonad (Env Term p n)
patternMatchList [] PNil = return zeroE
patternMatchList (e1 : es) (PCons p1 ps) = do
    env1 <- patternMatches e1 p1 
    env2 <- patternMatchList es ps
    withSNat (Pat.size ps) $
      return (env2 .++ env1)
patternMatchList _ _ = Env.err [DS "pattern match failure"]

{-
findBranch :: forall n. (SNatI n) => Term n -> [Match n] -> Maybe (Term n)
findBranch e [] = Nothing
findBranch e (Branch (bnd :: PatBind Term Term (Pattern p) n) : brs) =
  case patternMatches e (getPat bnd) e of
    Just r -> Just $ instantiatePat bnd r
    Nothing -> findBranch e brs
-}