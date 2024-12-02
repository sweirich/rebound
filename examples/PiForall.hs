-- A dependent type system, based on pi-forall (version4)
module PiForall where

import AutoEnv
import AutoEnv.Pat
import AutoEnv.Pat.Rebind
import Control.Monad (guard, zipWithM_)
import Control.Monad.Reader (MonadReader(local), asks, ReaderT(runReaderT))
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Data.Fin qualified
import Data.List qualified as List
import Data.Maybe qualified as Maybe
import Data.Vec qualified
import Text.ParserCombinators.Parsec.Pos (SourcePos, newPos)





{-

-------------------------------------------------------

-- * definitions for pattern matching

-------------------------------------------------------

instance Sized (PatList p) where
  type Size (PatList p) = p
  size PNil = s0
  size (PCons p ps) = sPlus (size ps) (size p)

-- we can count the number of variables bound in the pattern
-- (though we probably already know it)
instance Sized (Pattern p) where
  type Size (Pattern p) = p
  size :: Pattern p n -> SNat p
  size (PatCon _ l) = size l
  size PatVar = s1

-- >>> patternMatch pat0 tm0
-- Just [True,Bool]

patternMatchList :: (SNatI n) => PatList p n -> [Term n] -> Maybe (Env Term p n)
patternMatchList PNil [] = Just zeroE
patternMatchList (PCons p1 ps) (e1 : es) = undefined

{-
  case axiomAssoc of
    Refl -> do
            env1 <- patternMatch p1 e1
            env2 <- patternMatchList (applyE (env1 .++ idE) ps) es
            return (env2 .++ env1)
patternMatchList _ _ = Nothing
-}

-- | Compare a pattern with an expression, potentially
-- producing a substitution for all of the variables
-- bound in the pattern
patternMatch :: forall p n. (SNatI n) => Pattern p n -> Term n -> Maybe (Env Term p n)
patternMatch PatVar e = Just $ oneE e
patternMatch (PatCon l ps) (DataCon n args)
  | l == n = patternMatchList ps args
patternMatch _ _ = Nothing

findBranch :: forall n. (SNatI n) => Term n -> [Match n] -> Maybe (Term n)
findBranch e [] = Nothing
findBranch e (Branch (bnd :: PatBind Term Term (Pattern p) n) : brs) =
  case patternMatch (getPat bnd) e of
    Just r -> Just $ instantiatePat bnd r
    Nothing -> findBranch e brs



----------------------------------------------
-- Some Examples
----------------------------------------------

star :: Term n
star = Const Star

-- No annotation on the binder
lam :: Term (S n) -> Term n
lam b = Match [Branch (patBind PVar b)]

-- Annotation on the binder
alam :: Term n -> Term (S n) -> Term n
alam t b = Match [Branch (patBind (PAnnot PVar t) b)]

-- The identity function "λ x. x". With de Bruijn indices
-- we write it as "λ. 0", though with `Match` it looks a bit different
t0 :: Term Z
t0 = lam (Var f0)

-- A larger term "λ x. λy. x (λ z. z z)"
-- λ. λ. 1 (λ. 0 0)
t1 :: Term Z
t1 =
  lam
    ( lam
        (Var f1 `App` lam (Var f0 `App` Var f0))
    )

-- To show lambda terms, we can write a simple recursive instance of
-- Haskell's `Show` type class. In the case of a binder, we use the `unbind`
-- operation to access the body of the lambda expression.

-- >>> t0
-- λ_. 0

-- >>> t1
-- λ_. (λ_. (1 (λ_. (0 0))))

-- Polymorphic identity function and its type

tyid = Pi star (bind (Pi (Var f0) (bind (Var f1))))

tmid = lam (lam (Var f0))

-- >>> tyid
-- Pi *. 0 -> 1

-- >>> tmid
-- λ_. (λ_. 0)





--------------------------------------------------------

-- * big-step evaluation

--------------------------------------------------------

-- We can write the usual operations for evaluating
-- lambda terms to values

-- >>> eval t1
-- λ_. (λ_. (1 (λ_. (0 0))))

-- >>> eval (t1 `App` t0)
-- λ_. (λ_. 0 (λ_. (0 0)))

-- OLD
-- λ. λ. 0 (λ. 0 0)

eval :: (SNatI n) => Term n -> Term n
eval (Var x) = Var x
eval (Match b) = Match b
eval (App e1 e2) =
  let v = eval e2
   in case eval e1 of
        Match b -> case findBranch v b of
          Just e -> eval e
          Nothing -> error "pattern match failure"
        t -> App t v
eval (Const c) = Const c
eval (Pi a b) = Pi a b
eval (Sigma a b) = Sigma a b
eval (Annot a t) = eval a
eval (Pair a b) = Pair a b

-- small-step evaluation

-- >>> step (t1 `App` t0)
-- Just (λ_. (λ_. 0 (λ_. (0 0))))

step :: (SNatI n) => Term n -> Maybe (Term n)
step (Var x) = Nothing
step (Match b) = Nothing
step (App (Match bs) e2)
  | Just r <- findBranch e2 bs =
      Just r
step (App e1 e2)
  | Just e1' <- step e1 = Just (App e1' e2)
  | Just e2' <- step e2 = Just (App e1 e2')
  | otherwise = Nothing
step (Const _) = Nothing
step (Pi a b) = Nothing
step (Sigma a b) = Nothing
step (Pair a b) = Nothing
step (Annot a t) = step a

eval' :: (SNatI n) => Term n -> Term n
eval' e
  | Just e' <- step e = eval' e'
  | otherwise = e

----------------------------------------------------------------
-- Check for equality
----------------------------------------------------------------
data Err where
  NotEqual :: Term n -> Term n -> Err
  PiTermected :: Term n -> Err
  PiTermectedPat :: Pat p1 n1 -> Err
  SigmaTermected :: Term n -> Err
  VarEscapes :: Term n -> Err
  PatternMismatch :: Pat p1 n1 -> Pat p2 n2 -> Err
  PatternTypeMismatch :: Pat p1 n1 -> Term n1 -> Err
  AnnotationNeeded :: Term n -> Err
  AnnotationNeededPat :: Pat p1 n1 -> Err
  UnknownConst :: Const -> Err

deriving instance (Show Err)

-- find the head form
whnf :: (SNatI n) => Term n -> Term n
whnf (App a1 a2) = case whnf a1 of
  Match bs -> case findBranch (eval a2) bs of
    Just b -> whnf b
    Nothing -> App (Match bs) a2
  t -> App t a2
whnf (Annot a t) = whnf a
whnf a = a

equate :: (MonadError Err m, SNatI n) => Term n -> Term n -> m ()
equate t1 t2 = do
  let n1 = whnf t1
      n2 = whnf t2
  equateWHNF n1 n2

equatePat ::
  forall p1 p2 m n.
  (MonadError Err m, SNatI n) =>
  Pat p1 n ->
  Pat p2 n ->
  m ()
equatePat PVar PVar = pure ()
equatePat (PConst c1) (PConst c2) | c1 == c2 = pure ()
equatePat (PPair (Rebind p1 p1')) (PPair (Rebind p2 p2'))
  | Just Refl <- testEquality (size p1) (size p2) =
      withSNat (sPlus (size p1) (snat @n)) $
        equatePat p1 p2 >> equatePat p1' p2'
equatePat (PApp (Rebind p1 p2)) (PApp (Rebind p1' p2'))
  | Just Refl <- testEquality (size p1) (size p1') =
      withSNat (sPlus (size p1) (snat @n)) $
        equatePat p1 p1' >> equatePat p2 p2'
equatePat (PAnnot p1 e1) (PAnnot p2 e2) =
  equatePat p1 p2 >> equate e1 e2
equatePat p1 p2 = throwError (PatternMismatch p1 p2)

equateBranch :: (MonadError Err m, SNatI n) => Branch n -> Branch n -> m ()
equateBranch (Branch b1) (Branch b2) =
  unPatBind b1 $ \(p1 :: Pat p1 n) body1 ->
    unPatBind b2 $ \(p2 :: Pat p2 n) body2 ->
      case testEquality (size p1) (size p2) of
        Just Refl ->
          equatePat p1 p2 >> equate body1 body2
        Nothing ->
          throwError (PatternMismatch (getPat b1) (getPat b2))

equateWHNF :: (SNatI n, MonadError Err m) => Term n -> Term n -> m ()
equateWHNF n1 n2 =
  case (n1, n2) of
    (Const c1, Const c2) | c1 == c2 -> pure ()
    (Var x, Var y) | x == y -> pure ()
    (Match b1, Match b2) ->
      zipWithM_ equateBranch b1 b2
    (App a1 a2, App b1 b2) -> do
      equateWHNF a1 b1
      equate a2 b2
    (Pi tyA1 b1, Pi tyA2 b2) -> do
      equate tyA1 tyA2
      equate (unbind b1) (unbind b2)
    (Sigma tyA1 b1, Sigma tyA2 b2) -> do
      equate tyA1 tyA2
      equate (unbind b1) (unbind b2)
    (_, _) -> throwError (NotEqual n1 n2)

----------------------------------------------------------------

-- * Type checking

----------------------------------------------------------------

-- | infer the type of a constant term
-- TODO: use prelude, and allow datatypes to have parameters/telescopes
inferConst :: (MonadError Err m) => Const -> m (Term n)
inferConst Star = pure $ Const Star
inferConst (DataCon "True") = pure $ Const (TyCon "Bool")
inferConst (DataCon "False") = pure $ Const (TyCon "Bool")
inferConst (DataCon "()") = pure $ Const (TyCon "Unit")
inferConst (TyCon "Bool") = pure $ Const Star
inferConst (TyCon "Unit") = pure $ Const Star
inferConst c = throwError (UnknownConst c)

inferPattern ::
  (MonadError Err m, SNatI n) =>
  Ctx Term n -> -- input context
  Pat p n -> -- pattern to check
  m (Ctx Term (Plus p n), Term (Plus p n), Term n)
inferPattern g (PConst c) = do
  ty <- inferConst c
  pure (g, Const c, ty)
inferPattern g (PAnnot p ty) = do
  (g', e) <- checkPattern g p ty
  pure (g', e, ty)
inferPattern g p = throwError (AnnotationNeededPat p)

-- | type check a pattern and produce an extended typing context,
-- plus expression form of the pattern (for dependent pattern matching)

-- TODO: do we need to pass in the context? Can we just make it an
-- output of the function?
checkPattern ::
  forall m n p.
  (MonadError Err m, SNatI n) =>
  Ctx Term n -> -- input context
  Pat p n -> -- pattern to check
  Term n -> -- expected type of pattern (should be in whnf)
  m (Ctx Term (Plus p n), Term (Plus p n))
checkPattern g PVar a = do
  pure (g +++ a, var f0)
checkPattern g (PPair rb) (Sigma tyA tyB) =
  unRebind rb $ \p1 p2 -> do
    (g', e1) <- checkPattern g p1 tyA
    let tyB' = weakenBind' (size p1) tyB
    let tyB'' = whnf (instantiate tyB' e1)
    (g'', e2) <- checkPattern g' p2 tyB''
    let e1' = weaken' (size p2) e1
    return (g'', Pair e1' e2)
checkPattern g (PApp rb) ty =
  unRebind rb $ \p1 p2 -> do
    (g', e1, ty) <- inferPattern g p1
    case weaken' (size p1) (whnf ty) of
      Pi tyA tyB -> do
        (g'', e2) <- checkPattern g' p2 tyA
        equate (weaken' (size p1) ty) (instantiate tyB e1)
        let e1' = weaken' (size p2) e1
        return (g'', App e1' e2)
      _ -> throwError (PiTermectedPat p1)
checkPattern g p ty = do
  (g', e, ty') <- inferPattern g p
  equate ty ty'
  return (g', e)

-----------------------------------------------------------
-- Checking branches
-----------------------------------------------------------

--      G |- p : A => G'      G' |- b : B { p / x}
--   ----------------------------------------------
--       G |- p => b : Pi x : A . B

checkBranch ::
  forall m n.
  (MonadError Err m, SNatI n) =>
  Ctx Term n ->
  Term n ->
  Branch n ->
  m ()
checkBranch g (Pi tyA tyB) (Branch bnd) =
  unPatBind bnd $ \(pat :: Pat p n) body -> do
    let p = size pat

    -- find the extended context and pattern expression
    (g', a) <- checkPattern g pat tyA

    -- shift tyB to the scope of the pattern and instantiate it with 'a'
    -- must be done simultaneously because 'a' is from a larger scope
    let tyB' = instantiateShift p tyB a

    -- check the body of the branch in the scope of the pattern
    checkType g' body tyB'
checkBranch g t e = throwError (PiTermected t)

-- should only check with a type in whnf
checkType ::
  forall n m.
  (MonadError Err m, SNatI n) =>
  Ctx Term n ->
  Term n ->
  Term n ->
  m ()
checkType g (Pair a b) ty = do
  tyA <- inferType g a
  tyB <- inferType g b
  case ty of
    (Sigma tyA tyB) -> do
      checkType g a tyA
      checkType g b (instantiate tyB a)
    _ -> throwError (SigmaTermected ty)
checkType g (Match bs) ty = do
  mapM_ (checkBranch g ty) bs
checkType g e t1 = do
  t2 <- inferType g e
  equate (whnf t2) t1

-- | infer the type of an expression. This type may not
-- necessarily be in whnf
inferType ::
  forall n m.
  (MonadError Err m, SNatI n) =>
  Ctx Term n ->
  Term n ->
  m (Term n)
inferType g (Var x) = pure (applyEnv g x)
inferType g (Const c) = inferConst c
inferType g (Pi a b) = do
  checkType g a (Const Star)
  checkType (g +++ a) (unbind b) (Const Star)
  pure (Const Star)
inferType g (App a b) = do
  tyA <- inferType g a
  case whnf tyA of
    Pi tyA1 tyB1 -> do
      checkType g b tyA1
      pure $ instantiate tyB1 b
    t -> throwError (PiTermected t)
inferType g (Sigma a b) = do
  checkType g a (Const Star)
  checkType (g +++ a) (unbind b) (Const Star)
  pure (Const Star)
inferType g a =
  throwError (AnnotationNeeded a)

-- >>> tmid
-- λ_. (λ_. 0)

-- >>> tyid
-- Pi *. 0 -> 1

-- >>> :t tyid
-- tyid :: Term n

-- >>> (checkType zeroE tmid tyid :: Either Err ())
-- Right ()

-- >>> (inferType zeroE (App tmid tyid) :: Either Err (Term N0))
-- Left (AnnotationNeeded (λ_. (λ_. 0)))

-----------------------------------------------------------
-- Checking that pattern matching is exhaustive
-----------------------------------------------------------
-- (Work in progress)

-- | Given a particular type and a list of patterns, make
-- sure that the patterns cover all potential cases for that
-- type.
-- If the list of patterns starts with a variable, then it doesn't
-- matter what the type is, the variable is exhaustive. (This code
-- does not report unreachable patterns.)
-- Otherwise, the scrutinee type must be a type constructor, so the
-- code looks up the data constructors for that type and makes sure that
-- there are patterns for each one.
data PatAny n = forall p. PatAny (Pat p n)

extractPat :: Branch n -> PatAny n
extractPat (Branch bnd) = PatAny (getPat bnd)

lookupTyCon :: (MonadError Err m) => TyConName -> m DataDef
lookupTyCon tname =
  case List.find (\d -> data_name d == tname) prelude of
    Just dcon -> pure dcon
    Nothing -> throwError (UnknownConst (TyCon tname))

ensureTyCon :: (MonadError Err m) => Term n -> m (TyConName, [Term n])
ensureTyCon (Const (TyCon c)) = return (c, [])
ensureTyCon (App a1 a2) = do
  (c, args) <- ensureTyCon a1
  return (c, args ++ [a2])
ensureTyCon _ = error "not a tycon"

-}

{-
exhaustivityCheck :: (MonadError Err m) => Term n -> [PatAny n] -> m ()
exhaustivityCheck ty (PatAny PVar : _) = return ()
exhaustivityCheck (Sigma tyA tyB) [ PatAny (PPair rb) ] = do
    unRebind rb $ \p1 p2 -> do
       exhaustivityCheck tyA p1
exhaustivityCheck ty pats = do
    (tycon, tys) <- ensureTyCon ty
    datadef <- lookupTyCon tycon
    loop pats (data_constructors datadef) where
        loop :: [ PatAny n ] -> [ ConstructorDef n ] -> m ()
        loop = undefined
-}
