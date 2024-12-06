module PiForall.Equal where

import PiForall.Syntax
import PiForall.Environment (TcMonad )
import qualified PiForall.Environment as Env
import PiForall.PrettyPrint

import AutoEnv.Env as Env
import AutoEnv
import AutoEnv.Pat
import AutoEnv.Pat.LocalBind as L
import AutoEnv.Pat.Rebind



import Control.Monad(unless, zipWithM, zipWithM_)
import Control.Monad.Except (catchError)

-- | compare two expressions for equality
-- first check if they are alpha equivalent then
-- if not, weak-head normalize and compare
-- throw an error if they cannot be matched up
equate :: forall n. SNatI n => Term n -> Term n -> TcMonad ()
equate t1 t2 | t1 == t2 = return () 
equate t1 t2 = do
  n1 <- whnf t1  
  n2 <- whnf t2
  case (n1, n2) of 
    (TyType, TyType) -> return ()
    (Var x,  Var y) | x == y -> return ()
    (Lam bnd1, Lam bnd2) -> do
      equate @(S n) (L.unbind bnd1) (L.unbind bnd2)
    (App a1 a2, App b1 b2) ->
      equate a1 b1 >> equate a2 b2
    (Pi tyA1 bnd1, Pi tyA2 bnd2) -> do 
      equate tyA1 tyA2                                             
      equate (L.unbind bnd1) (L.unbind bnd2)
      
    (Let rhs1 bnd1, Let rhs2 bnd2) -> do
      equate rhs1 rhs2
      equate (L.unbind bnd1) (L.unbind bnd2)            
    (TyCon c1 ts1, TyCon c2 ts2) | c1 == c2 -> 
      zipWithM_ equateArgs [ts1] [ts2]
    (DataCon d1 a1, DataCon d2 a2) | d1 == d2 -> do
      equateArgs a1 a2
    (Case s1 brs1, Case s2 brs2) 
      | length brs1 == length brs2 -> do
      equate s1 s2
      -- require branches to be in the same order
      -- on both expressions
      let 
        matchBr :: Match n -> Match n -> TcMonad ()
        matchBr (Branch bnd1) (Branch bnd2) = 
            unPatBind bnd1 $ \p1 a1 -> 
            unPatBind bnd2 $ \p2 a2 ->
            case patEq p1 p2 of
              Just Refl -> equate a1 a2
              _ -> Env.err [DS "Cannot match branches in",
                              DD n1, DS "and", DD n2]
      zipWithM_ matchBr brs1 brs2       
    (_,_) -> tyErr n1 n2
 where tyErr n1 n2 = do 
          gamma <- Env.getLocalCtx
          Env.err [DS "Expected", DD n2,
               DS "but found", DD n1,
               DS "in context:", DD gamma]
       

{- SOLN EP -}
-- | Match up args
equateArgs :: SNatI n => [Term n] -> [Term n] -> TcMonad ()    
equateArgs (a1:t1s) (a2:t2s) = do
  equate a1 a2
  equateArgs t1s t2s
equateArgs [] [] = return ()
equateArgs a1 a2 = do 
          gamma <- Env.getLocalCtx
          Env.err [DS "Expected", DD (length a2),
                   DS "but found", DD (length a1),
                   DS "in context:", DD gamma]


-------------------------------------------------------

-- | Ensure that the given type 'ty' is some tycon applied to 
--  params (or could be normalized to be such)
-- Throws an error if this is not the case 
ensureTCon :: SNatI n => Term n -> TcMonad (TyConName, [Term n])
ensureTCon aty = do
  nf <- whnf aty
  case nf of 
    TyCon n params -> return (n, params)    
    _ -> Env.err [DS "Expected a data type but found", DD nf]
    
-------------------------------------------------------
-- | Convert a term to its weak-head normal form.             
-- | TODO: add explicit environment
whnf :: SNatI n => Term n -> TcMonad (Term n)
whnf (Var x) = do      
  maybeDef <- Env.lookupDef x
  case maybeDef of 
    (Just d) -> whnf d 
    _ -> return (Var x)
        
whnf (App t1 t2) = do
  nf <- whnf t1 
  case nf of 
    (Lam  bnd) -> do
      whnf (L.instantiate bnd t2)
    _ -> do
      return (App nf t2)
-- ignore/remove type annotations and source positions when normalizing  
whnf (Ann tm _) = whnf tm
whnf (Pos _ tm) = whnf tm
whnf (Let rhs bnd)  = do
  whnf (L.instantiate bnd rhs)
 
whnf (Case scrut mtchs) = do
  nf <- whnf scrut        
  case nf of 
    (DataCon d args) -> f mtchs where
      f (Branch bnd : alts) = (do
          let pat = getPat bnd
          ss <- patternMatches nf pat 
          whnf (instantiatePat bnd ss)) 
            `catchError` \ _ -> f alts
      f [] = Env.err $ [DS "Internal error: couldn't find a matching",
                    DS "branch for", DD nf, DS "in"] ++ map DD mtchs
    _ -> return (Case nf mtchs){- STUBWITH -}            
-- all other terms are already in WHNF
-- don't do anything special for them
whnf tm = return tm

-- | 'Unify' the two terms, producing a list of definitions that 
-- must hold for the terms to be equal
-- If the terms are already equal, succeed with an empty list
-- If there is an obvious mismatch, fail with an error
-- If either term is "ambiguous" (i.e. neutral), give up and 
-- succeed with an empty list
unify :: SNatI n => Term n -> Term n -> TcMonad [Local Z n]
unify tx ty = do
  txnf <- whnf tx
  tynf <- whnf ty
  if txnf == tynf
    then return []
    else case (txnf, tynf) of
      (Var x, Var y) | x == y -> return []
      (Var y, yty)   | not (y `appearsFree` yty)
              -> return [LocalDef y yty] 
      (yty, Var y)   | not (y `appearsFree` yty) 
              -> return [LocalDef y yty]
      (DataCon n1 a1, DataCon n2 a2) 
        | n1 == n2 ->  unifyArgs a1 a2
      (TyCon s1 tms1, TyCon s2 tms2)
        | s1 == s2 -> unifyArgs tms1 tms2
      (Lam bnd1, Lam bnd2) -> do
        locals <- unify (L.unbind bnd1) (L.unbind bnd2)
        -- TODO: make sure that we don't def the 
        -- bound variable
        undefined
      (Pi tyA1 bnd1, Pi tyA2 bnd2) -> do
        ds1 <- unify tyA1 tyA2
        ds2 <- unify (L.unbind bnd1) (L.unbind bnd2)
        let ds2' = undefined -- strengthen!!
        return (ds1 ++ ds2')
      _ ->
        if amb txnf || amb tynf
          then return []
          else Env.err [DS "Cannot equate", DD txnf, DS "and", DD tynf] 
  where
    unifyArgs (t1 : a1s) (t2 : a2s) = do
      ds <- unify t1 t2
      ds' <- unifyArgs a1s a2s
      return $ ds ++ ds'
    unifyArgs [] [] = return []
    unifyArgs _ _ = Env.err [DS "internal error (unify)"] 


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
-- producing a substitution for all of the variables
-- bound in the pattern
patternMatches :: forall p n. (SNatI n) => Term n -> Pattern p n -> TcMonad (Env Term p n)
patternMatches e (PatVar _) = return (oneE e)
patternMatches (DataCon n args) (PatCon l ps) 
  | l == n = patternMatchList args ps
patternMatches nf pat = Env.err [DS "arg", DD nf, DS "doesn't match pattern", DD pat]


patternMatchList :: (SNatI n) => [Term n] -> PatList p n -> TcMonad (Env Term p n)
patternMatchList [] PNil = return zeroE
patternMatchList (e1 : es) (PCons p1 ps)  = undefined
patternMatchList _ _ = Env.err []
{-
  case axiomAssoc of
    Refl -> do
            env1 <- patternMatch e1 p1 
            env2 <- patternMatchList es (applyE (env1 .++ idE) ps) 
            return (env2 .++ env1)
patternMatchList _ _ = Env.err []
-}

{-
findBranch :: forall n. (SNatI n) => Term n -> [Match n] -> Maybe (Term n)
findBranch e [] = Nothing
findBranch e (Branch (bnd :: PatBind Term Term (Pattern p) n) : brs) =
  case patternMatches e (getPat bnd) e of
    Just r -> Just $ instantiatePat bnd r
    Nothing -> findBranch e brs
-}