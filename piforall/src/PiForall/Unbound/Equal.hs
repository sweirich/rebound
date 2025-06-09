{- pi-forall language -}

-- | Compare two terms for equality
module PiForall.Unbound.Equal
  ( whnf,
    equate,
    unify,
    {- SOLN DATA -} ensureTCon {- STUBWITH -},
  )
where

import Control.Monad (foldM, unless, zipWithM, zipWithM_)
import Control.Monad.Except (ExceptT, MonadError, catchError)
import PiForall.Unbound.Environment (D (..), TcMonad)
import PiForall.Unbound.Environment qualified as Env
import PiForall.Unbound.Syntax
import Unbound.Generics.LocallyNameless qualified as Unbound

-- | compare two expressions for equality
-- first check if they are alpha equivalent then
-- if not, weak-head normalize and compare
-- throw an error if they cannot be matched up
equate :: Term -> Term -> TcMonad ()
equate t1 t2 | Unbound.aeq t1 t2 = return ()
equate t1 t2 = do
  n1 <- whnf t1
  n2 <- whnf t2
  case (n1, n2) of
    (TyType, TyType) -> return ()
    (Var x, Var y) | x == y -> return ()
    (Lam ep1 bnd1, Lam ep2 bnd2) -> do
      (_, b1, b2) <- unbind2 bnd1 bnd2
      unless (ep1 == ep2) $
        tyErr n1 n2
      equate b1 b2
    (App a1 a2, App b1 b2) ->
      equate a1 b1 >> equateArg a2 b2
    (TyPi ep1 tyA1 bnd1, TyPi ep2 tyA2 bnd2) -> do
      (_, tyB1, tyB2) <- unbind2 bnd1 bnd2
      unless (ep1 == ep2) $
        tyErr n1 n2
      equate tyA1 tyA2
      equate tyB1 tyB2
    (TrustMe, TrustMe) -> return ()
    (PrintMe, PrintMe) -> return ()
    (TyEq a b, TyEq c d) -> do
      equate a c
      equate b d
    (Refl, Refl) -> return ()
    (Subst at1 pf1, Subst at2 pf2) -> do
      equate at1 at2
      equate pf1 pf2
    (Contra a1, Contra a2) ->
      equate a1 a2
    (TyCon c1 ts1, TyCon c2 ts2)
      | c1 == c2 ->
          zipWithM_ equateArgs [ts1] [ts2]
    (DataCon d1 a1, DataCon d2 a2) | d1 == d2 -> do
      equateArgs a1 a2
    (Case s1 brs1, Case s2 brs2)
      | length brs1 == length brs2 -> do
          equate s1 s2
          -- require branches to be in the same order
          -- on both expressions
          let matchBr (Match bnd1) (Match bnd2) = do
                mpb <- Unbound.unbind2 bnd1 bnd2
                case mpb of
                  Just (p1, a1, p2, a2) | p1 == p2 -> do
                    equate a1 a2
                  _ -> do
                    (p1, _) <- Unbound.unbind bnd1
                    (p2, _) <- Unbound.unbind bnd2
                    Env.err
                      [ DS "Cannot match branches in",
                        DN n1,
                        DS "and",
                        DN n2
                      ]
          zipWithM_ matchBr brs1 brs2
    (_, _) -> tyErr n1 n2
  where
    tyErr :: Term -> Term -> TcMonad ()
    tyErr n1 n2 = do
      gamma <- Env.getLocalCtx
      Env.err
        [ DS "Expected",
          DN n2,
          DS "but found",
          DN n1,
          DS "in context:",
          DN gamma
        ]

-- | Match up args
equateArgs :: [Arg] -> [Arg] -> TcMonad ()
equateArgs (a1 : t1s) (a2 : t2s) = do
  equateArg a1 a2
  equateArgs t1s t2s
equateArgs [] [] = return ()
equateArgs a1 a2 = do
  gamma <- Env.getLocalCtx
  Env.err
    [ DS "Expected",
      DC (length a2),
      DS "but found",
      DC (length a1),
      DS "in context:",
      DN gamma
    ]

-- | Ignore irrelevant arguments when comparing
equateArg :: Arg -> Arg -> TcMonad ()
equateArg (Arg Rel t1) (Arg Rel t2) = equate t1 t2
equateArg (Arg Irr t1) (Arg Irr t2) = return ()
equateArg (Arg _ a1) (Arg _ a2) =
  Env.err
    [ DS "Arg stage mismatch",
      DS "Expected ",
      DN a2,
      DS "Found ",
      DN a1
    ]

-------------------------------------------------------

-- | Ensure that the given type 'ty' is some tycon applied to
--  params (or could be normalized to be such)
-- Throws an error if this is not the case
ensureTCon :: Term -> TcMonad (TyConName, [Arg])
ensureTCon aty = do
  nf <- whnf aty
  case nf of
    TyCon n params -> return (n, params)
    _ -> Env.err [DS "Expected a data type but found", DN nf]

-------------------------------------------------------

-- | Convert a term to its weak-head normal form.
whnf :: Term -> TcMonad Term
whnf (Var x) = do
  maybeDef <- Env.lookupDef x
  case maybeDef of
    (Just d) -> whnf d
    _ -> return (Var x)
whnf (App t1 t2) = do
  nf <- whnf t1
  case nf of
    (Lam ep bnd) -> do
      whnf (instantiate bnd (unArg t2))
    _ -> do
      return (App nf t2)
-- ignore/remove type annotations and source positions when normalizing
whnf (Ann tm _) = whnf tm
whnf (Pos _ tm) = whnf tm
whnf (Let rhs bnd) = do
  whnf (instantiate bnd rhs)
whnf (Subst tm pf) = do
  pf' <- whnf pf
  case pf' of
    Refl -> whnf tm
    _ -> return (Subst tm pf')
whnf (Case scrut mtchs) = do
  nf <- whnf scrut
  case nf of
    (DataCon d args) -> f mtchs
      where
        f (Match bnd : alts) =
          ( do
              (pat, br) <- Unbound.unbind bnd
              ss <- patternMatches (Arg Rel nf) pat
              whnf (Unbound.substs ss br)
          )
            `catchError` \_ -> f alts
        f [] =
          Env.err $
            [ DS "Internal error: couldn't find a matching",
              DS "branch for",
              DN nf,
              DS "in"
            ]
              ++ map DN mtchs
    _ -> return (Case nf mtchs)
-- all other terms are already in WHNF
-- don't do anything special for them
whnf tm = return tm

-- | 'Unify' the two terms, producing a list of definitions that
-- must hold for the terms to be equal
-- If the terms are already equal, succeed with an empty list
-- If there is an obvious mismatch, fail with an error
-- If either term is "ambiguous" (i.e. neutral), give up and
-- succeed with an empty list
unify :: [TName] -> Term -> Term -> TcMonad [Entry]
unify ns tx ty = do
  txnf <- whnf tx
  tynf <- whnf ty
  if Unbound.aeq txnf tynf
    then return []
    else case (txnf, tynf) of
      (Var x, Var y) | x == y -> return []
      (Var y, yty) | y `notElem` ns -> return [Def y yty]
      (yty, Var y) | y `notElem` ns -> return [Def y yty]
      (TyEq a1 a2, TyEq b1 b2) -> (++) <$> unify ns a1 b1 <*> unify ns a2 b2
      (TyCon s1 tms1, TyCon s2 tms2)
        | s1 == s2 -> unifyArgs tms1 tms2
      (DataCon s1 a1s, DataCon s2 a2s)
        | s1 == s2 -> unifyArgs a1s a2s
      (Lam ep1 bnd1, Lam ep2 bnd2) -> do
        (x, b1, b2) <- unbind2 bnd1 bnd2
        unless (ep1 == ep2) $ do
          Env.err [DS "Cannot equate", DN txnf, DS "and", DN tynf]
        unify (x : ns) b1 b2
      (TyPi ep1 tyA1 bnd1, TyPi ep2 tyA2 bnd2) -> do
        (x, tyB1, tyB2) <- unbind2 bnd1 bnd2
        unless (ep1 == ep2) $ do
          Env.err [DS "Cannot equate", DN txnf, DS "and", DN tynf]
        ds1 <- unify ns tyA1 tyA2
        ds2 <- unify (x : ns) tyB1 tyB2
        return (ds1 ++ ds2)
      _ ->
        if amb txnf || amb tynf
          then return []
          else Env.err [DS "Cannot equate", DN txnf, DS "and", DN tynf]
  where
    unifyArgs (Arg _ t1 : a1s) (Arg _ t2 : a2s) = do
      ds <- unify ns t1 t2
      ds' <- unifyArgs a1s a2s
      return $ ds ++ ds'
    unifyArgs [] [] = return []
    unifyArgs _ _ = Env.err [DS "internal error (unify)"]

-- | Is a term "ambiguous" when it comes to unification?
-- In general, elimination forms are ambiguous because there are multiple
-- solutions.
amb :: Term -> Bool
amb (App t1 t2) = True
amb (Case _ _) = True
amb (Subst _ _) = True
amb _ = False

-- | Determine whether the pattern matches the argument
-- If so return the appropriate substitution
-- otherwise throws an error
patternMatches :: Arg -> Pattern -> TcMonad [(TName, Term)]
patternMatches (Arg _ t) (PatVar x) = return [(x, t)]
patternMatches (Arg Rel t) pat = do
  nf <- whnf t
  case (nf, pat) of
    (DataCon d [], PatCon d' pats) | d == d' -> return []
    (DataCon d args, PatCon d' pats)
      | d == d' ->
          concat <$> zipWithM patternMatches args (map fst pats)
    _ -> Env.err [DS "arg", DN nf, DS "doesn't match pattern", DN pat]
patternMatches (Arg Irr _) pat = do
  Env.err [DS "Cannot match against irrelevant args"]
