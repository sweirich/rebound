-- A dependent type system, with nested dependent pattern matching
-- This is an advanced usage of the binding library 
-- It doesn't correspond to any current system, but has its own elegance
-- (Maybe deserves to be written up on its own?)
-- However, this implementation does not attempt to use explicit environments
-- to optimize the execution.
module DepMatch where

import AutoEnv
import AutoEnv.Context

import qualified AutoEnv.Bind as B
import qualified AutoEnv.Pat.Scoped as Pat
import qualified AutoEnv.Pat.PatN as PN

import Control.Monad (guard, zipWithM_)
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Data.Fin qualified
import Data.List qualified as List
import Data.Maybe qualified as Maybe
import Data.Vec qualified
import Debug.Trace
import Text.ParserCombinators.Parsec.Pos (SourcePos, newPos)

-- | constants: universes, data constructors and type constructors
data Const = Star | DataCon DataConName | TyCon TyConName
  deriving (Eq)

-- | names of type constructors, like 'list'
type TyConName = String

-- | names of data constructors, like 'cons'
type DataConName = String

-- In this system, `Match` introduces a Pi type and generalizes 
-- dependent functions
-- If the pattern is a single variable, or an annotated variable,
-- then the Match term is just a normal lambda expression. 
-- But the pattern could be more structured than that, supporting 
-- a general form of pattern matching
data Exp (n :: Nat)
  = Const Const
  | Pi (Exp n) (B.Bind Exp Exp n)
  | Var (Fin n)
  | Match [Branch n]  -- n-way abstractions
  | App (Exp n) (Exp n)
  | Sigma (Exp n) (B.Bind Exp Exp n)
  | Pair (Exp n) (Exp n)
  | Annot (Exp n) (Exp n)

-- | A single branch in a match expression. Binds a pattern
-- with expression variables, within some expression body
data Branch (n :: Nat)
  = forall p. Branch (Pat.Bind Exp Exp (Pat p) n)


-- | Patterns, which may include embedded type annotations
-- `p` is the number of variables bound by the pattern
-- `n` is the number of free variables in type annotations in the pattern
-- Patterns are "telescopic"
-- In App/Pair pattern, we increase the scope so that variables
-- bound in the left subterm can be referred to in the right subterm.
data Pat (p :: Nat) (n :: Nat) where
  PConst :: Const -> Pat N0 n
  PVar :: Pat N1 n
  PApp :: Pat.Rebind (Pat p1) (Pat p2) n -> Pat (Plus p2 p1) n
  PPair :: Pat.Rebind (Pat p1) (Pat p2) n -> Pat (Plus p2 p1) n
  PAnnot :: Pat p n -> Exp n -> Pat p n


-- This definitions support telescopes: variables bound earlier in the pattern
-- can appear later.  For example, the pattern for a type paired with 
-- a term of that type can look like this 
--     (x, (y :: x)) 
-- The type of this pattern is
--     Sigma x:Star.x
-- "Rebind" creates a pair where the pattern variables
-- in the first component are bound in expression parts of the
-- second component
pat0 :: Pat N2 N0
pat0 = PPair (Pat.Rebind PVar (PAnnot PVar (Var f0)))

-------------------------------------------------------
-- definitions for pattern matching
-------------------------------------------------------

-- For any pattern type, we need to be able to calculate
-- the number of binding variables, both statically and dynamically
instance Pat.Sized (Pat p) where
  type Size (Pat p) = p
  size :: Pat p n -> SNat p
  size (PConst i) = s0
  size PVar = s1
  size (PApp rb) = Pat.size rb
  size (PPair rb) = Pat.size rb
  size (PAnnot p _) = Pat.size p

tm0 :: Exp Z
tm0 = Pair (Const (TyCon "Bool")) (Const (DataCon "True"))

-- >>> patternMatch pat0 tm0
-- Just [True,Bool]

-- | Compare a pattern with an expression, potentially
-- producing a substitution for all of the variables
-- bound in the pattern
patternMatch :: forall p n. (SNatI n) => Pat p n -> Exp n -> Maybe (Env Exp p n)
patternMatch PVar e = Just $ oneE e
patternMatch (PApp rb) (App e1 e2) = Pat.unRebind rb $ \p1 p2 -> do
  env1 <- patternMatch p1 e1
  -- NOTE: substitute in p2 with env1 before pattern matching
  let p2' = applyE (env1 .++ idE) p2
  env2 <- patternMatch p2' e2
  return (env2 .++ env1)
patternMatch (PConst s1) (Const s2) | s1 == s2 = Just zeroE
patternMatch (PPair rb) (Pair e1 e2) = Pat.unRebind rb $ \p1 p2 -> do
  env1 <- patternMatch p1 e1
  env2 <- patternMatch (applyE (env1 .++ idE) p2) e2
  return (env2 .++ env1)
-- ignore type annotates when pattern matching
patternMatch (PAnnot p _) e = patternMatch p e
patternMatch p (Annot e _) = patternMatch p e
patternMatch _ _ = Nothing

findBranch :: forall n. (SNatI n) => Exp n -> [Branch n] -> Maybe (Exp n)
findBranch e [] = Nothing
findBranch e (Branch (bnd :: Pat.Bind Exp Exp (Pat p) n) : brs) =
  case patternMatch (Pat.getPat bnd) e of
    Just r -> Just $ Pat.instantiate bnd r
    Nothing -> findBranch e brs

----------------------------------------------

-- * Subst instances

instance SubstVar Exp where
  var = Var

instance Subst Exp Exp where
  applyE r (Const c) = Const c
  applyE r (Pi a b) = Pi (applyE r a) (applyE r b)
  applyE r (Var x) = applyEnv r x
  applyE r (App e1 e2) = App (applyE r e1) (applyE r e2)
  applyE r (Sigma a b) = Sigma (applyE r a) (applyE r b)
  applyE r (Pair a b) = Pair (applyE r a) (applyE r b)
  applyE r (Match brs) = Match (map (applyE r) brs)
  applyE r (Annot a t) = Annot (applyE r a) (applyE r t)

instance Subst Exp (Pat p) where
  applyE :: Env Exp n m -> Pat p n -> Pat p m
  applyE r (PConst c) = PConst c
  applyE r PVar = PVar
  applyE r (PApp rb) = PApp (applyE r rb)
  applyE r (PPair rb) = PPair (applyE r rb)
  applyE r (PAnnot p t) = PAnnot (applyE r p) (applyE r t)

instance Subst Exp Branch where
  applyE :: forall n m. Env Exp n m -> Branch n -> Branch m
  applyE r (Branch b) = Branch (applyE r b)

----------------------------------------------
-- Free variable calculation
----------------------------------------------

t00 :: Exp N2
t00 = App (Var f0) (Var f0)

t01 :: Exp N2
t01 = App (Var f0) (Var f1)

-- >>> appearsFree f0 t00
-- True

-- >>> appearsFree f1 t00
-- False

instance FV Exp where
  appearsFree n (Var x) = n == x
  appearsFree n (Const c) = False
  appearsFree n (Pi a b) = appearsFree n a || appearsFree (FS n) (B.unbind b)
  appearsFree n (App a b) = appearsFree n a || appearsFree n b
  appearsFree n (Sigma a b) = appearsFree n a || appearsFree (FS n) (B.unbind b)
  appearsFree n (Pair a b) = appearsFree n a || appearsFree n b
  appearsFree n (Match b) = any (appearsFree n) b
  appearsFree n (Annot a t) = appearsFree n a || appearsFree n t

instance FV Branch where
  appearsFree n (Branch bnd) = appearsFree n bnd

instance FV (Pat p) where
  appearsFree n PVar = False
  appearsFree n (PConst _) = False
  appearsFree n (PApp rb) = appearsFree n rb
  appearsFree n (PPair rb) = appearsFree n rb
  appearsFree n (PAnnot p t) = appearsFree n p || appearsFree n t

----------------------------------------------
-- weakening (convenience functions)
----------------------------------------------

-- >>> :t weaken' s1 t00
-- weaken' s1 t00 :: Exp ('S ('S N1))

-- >>> weaken' s1 t00
-- 0 0

weaken' :: SNat m -> Exp n -> Exp (Plus m n)
weaken' m = applyE @Exp (weakenE' m)

weakenBind' :: SNat m -> B.Bind Exp Exp n -> B.Bind Exp Exp (Plus m n)
weakenBind' m = applyE @Exp (weakenE' m)

----------------------------------------------
-- strengthening
----------------------------------------------

-- >>> strengthen' s1 s1 t00
-- Just (0 0)

-- >>> strengthen' s1 s1 t01
-- Nothing

instance Strengthen Exp where
  -- strengthen' :: SNat m -> SNat n -> Exp (Plus m n) -> Maybe (Exp n)
  strengthen' m n (Var x) = Var <$> strengthen' m n x
  strengthen' m n (Const c) = pure (Const c)
  strengthen' m n (Pi a b) = Pi <$> strengthen' m n a <*> strengthen' m n b
  strengthen' m n (App a b) = App <$> strengthen' m n a <*> strengthen' m n b
  strengthen' m n (Pair a b) = Pair <$> strengthen' m n a <*> strengthen' m n b
  strengthen' m n (Sigma a b) = Sigma <$> strengthen' m n a <*> strengthen' m n b
  strengthen' m n (Match b) = Match <$> mapM (strengthen' m n) b
  strengthen' m n (Annot a t) = Annot <$> strengthen' m n a <*> strengthen' m n t

instance Strengthen (Pat p) where
  strengthen' :: forall m n p. SNat m -> SNat n -> Pat p (Plus m n) -> Maybe (Pat p n)
  strengthen' m n PVar = pure PVar
  strengthen' m n (PConst c) = pure (PConst c)
  strengthen' m n (PApp rb) = PApp <$> strengthen' m n rb
  strengthen' m n (PPair rb) = PPair <$> strengthen' m n rb
  strengthen' m n (PAnnot p1 e2) =
    PAnnot
      <$> strengthen' m n p1
      <*> strengthen' m n e2

instance Strengthen Branch where
  strengthen' m n (Branch bnd) = Branch <$> strengthen' m n bnd

----------------------------------------------
-- Some Examples
----------------------------------------------

star :: Exp n
star = Const Star

-- No annotation on the binder
lam :: Exp (S n) -> Exp n
lam b = Match [Branch (Pat.bind PVar b)]

-- Annotation on the binder
alam :: Exp n -> Exp (S n) -> Exp n
alam t b = Match [Branch (Pat.bind (PAnnot PVar t) b)]

-- The identity function "λ x. x". With de Bruijn indices
-- we write it as "λ. 0", though with `Match` it looks a bit different
t0 :: Exp Z
t0 = lam (Var f0)

-- A larger term "λ x. λy. x (λ z. z z)"
-- λ. λ. 1 (λ. 0 0)
t1 :: Exp Z
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

tyid = Pi star (B.bind (Pi (Var f0) (B.bind (Var f1))))

tmid = lam (lam (Var f0))

-- >>> tyid
-- Pi *. 0 -> 1

-- >>> tmid
-- λ_. (λ_. 0)

--------------------------------------------------------

-- * Show instances

--------------------------------------------------------

instance Show Const where
  show Star = "*"
  show (DataCon s) = s
  show (TyCon s) = s

instance Show (Exp n) where
  showsPrec :: Int -> Exp n -> String -> String
  showsPrec _ (Const c) = showString (show c)
  showsPrec d (Pi a b)
    | appearsFree FZ (B.unbind b) =
        showParen (d > 10) $
          showString "Pi "
            . shows a
            . showString ". "
            . shows (B.unbind b)
    | otherwise =
        showParen (d > 10) $
          showsPrec 11 a
            . showString " -> "
            . showsPrec 10 (B.unbind b)
  showsPrec d (Sigma a b)
    | appearsFree FZ (B.unbind b) =
        showParen (d > 10) $
          showString "Sigma "
            . shows a
            . showString ". "
            . shows (B.unbind b)
    | otherwise =
        showParen (d > 10) $
          showsPrec 11 a
            . showString " * "
            . showsPrec 10 (B.unbind b)
  showsPrec _ (Var x) = shows (toInt x)
  showsPrec d (App e1 e2) =
    showParen (d > 0) $
      showsPrec 10 e1
        . showString " "
        . showsPrec 11 e2
  showsPrec d (Pair e1 e2) =
    showParen (d > 0) $
      showsPrec 10 e1
        . showString ", "
        . showsPrec 11 e2
  showsPrec d (Match [b]) =
    showParen (d > 10) $
      showString "λ"
        . showsPrec 10 b
  showsPrec d (Match b) =
    showParen (d > 10) $
      showString "match"
        . showsPrec 10 b
  showsPrec d (Annot a t) =
    showParen (d > 10) $
      showsPrec 10 a
        . showString " : "
        . showsPrec 10 t

instance Show (Branch b) where
  showsPrec d (Branch b) =
    showsPrec 10 (Pat.getPat b)
      . showString ". "
      . showsPrec 11 (Pat.getBody b)

instance Show (Pat p n) where
  showsPrec d PVar = showString "_"
  showsPrec d (PConst c) = showsPrec d c
  showsPrec d (PApp (Pat.Rebind e1 e2)) =
    showParen (d > 0) $
      showsPrec 10 e1
        . showString " "
        . showsPrec 11 e2
  showsPrec d (PPair (Pat.Rebind e1 e2)) =
    showParen (d > 0) $
      showsPrec 10 e1
        . showString ", "
        . showsPrec 11 e2
  showsPrec d (PAnnot e1 e2) =
    showParen (d > 0) $
      showsPrec 10 e1
        . showString " : "
        . showsPrec 11 e2

--------------------------------------------------------

-- * Alpha equivalence

--------------------------------------------------------

-- NOTE: this is not the same type as patEq
testEquality2 :: Pat p1 n -> Pat p2 n -> Maybe (p1 :~: p2)
testEquality2 PVar PVar = Just Refl
testEquality2 (PApp (Pat.Rebind p1 p2)) (PApp (Pat.Rebind p1' p2')) = do
  Refl <- testEquality2 p1 p1'
  Refl <- testEquality2 p2 p2'
  return Refl
testEquality2 (PPair (Pat.Rebind p1 p2)) (PPair (Pat.Rebind p1' p2')) = do
  Refl <- testEquality2 p1 p1'
  Refl <- testEquality2 p2 p2'
  return Refl
testEquality2 (PAnnot p1 p2) (PAnnot p1' p2') = do
  Refl <- testEquality2 p1 p1'
  guard (p2 == p2')
  return Refl
testEquality2 (PConst s1) (PConst s2) | s1 == s2 = Just Refl
testEquality2 _ _ = Nothing

instance Eq (Branch n) where
  (==) :: Branch n -> Branch n -> Bool
  (Branch (p1 :: Pat.Bind Exp Exp (Pat m1) n))
    == (Branch (p2 :: Pat.Bind Exp Exp (Pat m2) n)) =
      case testEquality
        (Pat.size (Pat.getPat p1) :: SNat m1)
        (Pat.size (Pat.getPat p2) :: SNat m2) of
        Just Refl -> p1 == p2
        Nothing -> False

-- To compare pattern binders, we need to unbind, but also
-- make sure that the patterns are equal
instance (Eq (Exp n)) => Eq (Pat.Bind Exp Exp (Pat m) n) where
  b1 == b2 =
    Maybe.isJust (testEquality2 (Pat.getPat b1) (Pat.getPat b2))
      && Pat.getBody b1 == Pat.getBody b2

-- To compare binders, we only need to `unbind` them
instance (Eq (Exp n)) => Eq (B.Bind Exp Exp n) where
  b1 == b2 = B.unbind b1 == B.unbind b2

instance (Eq (Exp n)) => Eq (PN.Bind2 Exp Exp n) where
  b1 == b2 = PN.unbind2 b1 == PN.unbind2 b2

-- With the instance above the derivable equality instance
-- is alpha-equivalence
deriving instance (Eq (Exp n))

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

eval :: (SNatI n) => Exp n -> Exp n
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

step :: (SNatI n) => Exp n -> Maybe (Exp n)
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

eval' :: (SNatI n) => Exp n -> Exp n
eval' e
  | Just e' <- step e = eval' e'
  | otherwise = e

----------------------------------------------------------------
-- Check for equality
----------------------------------------------------------------
data Err where
  NotEqual :: Exp n -> Exp n -> Err
  PiExpected :: Exp n -> Err
  PiExpectedPat :: Pat p1 n1 -> Err
  SigmaExpected :: Exp n -> Err
  VarEscapes :: Exp n -> Err
  PatternMismatch :: Pat p1 n1 -> Pat p2 n2 -> Err
  PatternTypeMismatch :: Pat p1 n1 -> Exp n1 -> Err
  AnnotationNeeded :: Exp n -> Err
  AnnotationNeededPat :: Pat p1 n1 -> Err
  UnknownConst :: Const -> Err

deriving instance (Show Err)

-- find the head form
whnf :: (SNatI n) => Exp n -> Exp n
whnf (App a1 a2) = case whnf a1 of
  Match bs -> case findBranch (eval a2) bs of
    Just b -> whnf b
    Nothing -> App (Match bs) a2
  t -> App t a2
whnf (Annot a t) = whnf a
whnf a = a

equate :: (MonadError Err m, SNatI n) => Exp n -> Exp n -> m ()
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
equatePat (PPair (Pat.Rebind p1 p1')) (PPair (Pat.Rebind p2 p2'))
  | Just Refl <- testEquality (Pat.size p1) (Pat.size p2) =
      withSNat (sPlus (Pat.size p1) (snat @n)) $
        equatePat p1 p2 >> equatePat p1' p2'
equatePat (PApp (Pat.Rebind p1 p2)) (PApp (Pat.Rebind p1' p2'))
  | Just Refl <- testEquality (Pat.size p1) (Pat.size p1') =
      withSNat (sPlus (Pat.size p1) (snat @n)) $
        equatePat p1 p1' >> equatePat p2 p2'
equatePat (PAnnot p1 e1) (PAnnot p2 e2) =
  equatePat p1 p2 >> equate e1 e2
equatePat p1 p2 = throwError (PatternMismatch p1 p2)

equateBranch :: (MonadError Err m, SNatI n) => Branch n -> Branch n -> m ()
equateBranch (Branch b1) (Branch b2) =
  Pat.unbind b1 $ \(p1 :: Pat p1 n) body1 ->
    Pat.unbind b2 $ \(p2 :: Pat p2 n) body2 ->
      case testEquality (Pat.size p1) (Pat.size p2) of
        Just Refl ->
          equatePat p1 p2 >> equate body1 body2
        Nothing ->
          throwError (PatternMismatch (Pat.getPat b1) (Pat.getPat b2))

equateWHNF :: (SNatI n, MonadError Err m) => Exp n -> Exp n -> m ()
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
      equate (B.unbind b1) (B.unbind b2)
    (Sigma tyA1 b1, Sigma tyA2 b2) -> do
      equate tyA1 tyA2
      equate (B.unbind b1) (B.unbind b2)
    (_, _) -> throwError (NotEqual n1 n2)

----------------------------------------------------------------

-- * Type checking

----------------------------------------------------------------

-- | infer the type of a constant term
-- TODO: use prelude, and allow datatypes to have parameters/telescopes
inferConst :: (MonadError Err m) => Const -> m (Exp n)
inferConst Star = pure $ Const Star
inferConst (DataCon "True") = pure $ Const (TyCon "Bool")
inferConst (DataCon "False") = pure $ Const (TyCon "Bool")
inferConst (DataCon "()") = pure $ Const (TyCon "Unit")
inferConst (TyCon "Bool") = pure $ Const Star
inferConst (TyCon "Unit") = pure $ Const Star
inferConst c = throwError (UnknownConst c)

inferPattern ::
  (MonadError Err m, SNatI n) =>
  Ctx Exp n -> -- input context
  Pat p n -> -- pattern to check
  m (Ctx Exp (Plus p n), Exp (Plus p n), Exp n)
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
  Ctx Exp n -> -- input context
  Pat p n -> -- pattern to check
  Exp n -> -- expected type of pattern (should be in whnf)
  m (Ctx Exp (Plus p n), Exp (Plus p n))
checkPattern g PVar a = do
  pure (g +++ a, var f0)
checkPattern g (PPair rb) (Sigma tyA tyB) =
  Pat.unRebind rb $ \p1 p2 -> do
    (g', e1) <- checkPattern g p1 tyA
    let tyB' = weakenBind' (Pat.size p1) tyB
    let tyB'' = whnf (B.instantiate tyB' e1)
    (g'', e2) <- checkPattern g' p2 tyB''
    let e1' = weaken' (Pat.size p2) e1
    return (g'', Pair e1' e2)
checkPattern g (PApp rb) ty =
  Pat.unRebind rb $ \p1 p2 -> do
    (g', e1, ty) <- inferPattern g p1
    case weaken' (Pat.size p1) (whnf ty) of
      Pi tyA tyB -> do
        (g'', e2) <- checkPattern g' p2 tyA
        equate (weaken' (Pat.size p1) ty) (B.instantiate tyB e1)
        let e1' = weaken' (Pat.size p2) e1
        return (g'', App e1' e2)
      _ -> throwError (PiExpectedPat p1)
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
  Ctx Exp n ->
  Exp n ->
  Branch n ->
  m ()
checkBranch g (Pi tyA tyB) (Branch bnd) =
  Pat.unbind bnd $ \(pat :: Pat p n) body -> do
    let p = Pat.size pat

    -- find the extended context and pattern expression
    (g', a) <- checkPattern g pat tyA

    -- shift tyB to the scope of the pattern and instantiate it with 'a'
    -- must be done simultaneously because 'a' is from a larger scope
    let tyB' = B.instantiateShift p tyB a

    -- check the body of the branch in the scope of the pattern
    checkType g' body tyB'
checkBranch g t e = throwError (PiExpected t)

-- should only check with a type in whnf
checkType ::
  forall n m.
  (MonadError Err m, SNatI n) =>
  Ctx Exp n ->
  Exp n ->
  Exp n ->
  m ()
checkType g (Pair a b) ty = do
  tyA <- inferType g a
  tyB <- inferType g b
  case ty of
    (Sigma tyA tyB) -> do
      checkType g a tyA
      checkType g b (B.instantiate tyB a)
    _ -> throwError (SigmaExpected ty)
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
  Ctx Exp n ->
  Exp n ->
  m (Exp n)
inferType g (Var x) = pure (applyEnv g x)
inferType g (Const c) = inferConst c
inferType g (Pi a b) = do
  checkType g a (Const Star)
  checkType (g +++ a) (B.unbind b) (Const Star)
  pure (Const Star)
inferType g (App a b) = do
  tyA <- inferType g a
  case whnf tyA of
    Pi tyA1 tyB1 -> do
      checkType g b tyA1
      pure $ B.instantiate tyB1 b
    t -> throwError (PiExpected t)
inferType g (Sigma a b) = do
  checkType g a (Const Star)
  checkType (g +++ a) (B.unbind b) (Const Star)
  pure (Const Star)
inferType g a =
  throwError (AnnotationNeeded a)

-- >>> tmid
-- λ_. (λ_. 0)

-- >>> tyid
-- Pi *. 0 -> 1

-- >>> :t tyid
-- tyid :: Exp n

-- >>> (checkType zeroE tmid tyid :: Either Err ())
-- Right ()

-- >>> (inferType zeroE (App tmid tyid) :: Either Err (Exp N0))
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
extractPat (Branch bnd) = PatAny (Pat.getPat bnd)

lookupTyCon :: (MonadError Err m) => TyConName -> m DataDef
lookupTyCon tname =
  case List.find (\d -> data_name d == tname) prelude of
    Just dcon -> pure dcon
    Nothing -> throwError (UnknownConst (TyCon tname))

ensureTyCon :: (MonadError Err m) => Exp n -> m (TyConName, [Exp n])
ensureTyCon (Const (TyCon c)) = return (c, [])
ensureTyCon (App a1 a2) = do
  (c, args) <- ensureTyCon a1
  return (c, args ++ [a2])
ensureTyCon _ = error "not a tycon"

{-
exhaustivityCheck :: (MonadError Err m) => Exp n -> [PatAny n] -> m ()
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

-------------------------------------------------------
-- Data types
-------------------------------------------------------

-- a telescope defined in scope n that
-- itself introduces m arguments
data Telescope m n where
  None :: Telescope Z n
  (:<>) :: Telescope m n -> Exp (Plus m n) -> Telescope (S m) n

data DataDef = forall n.
  Data
  { data_name :: TyConName,
    data_params :: Telescope n Z,
    data_sort :: Const,
    data_constructors :: [ConstructorDef n]
  }

data ConstructorDef n = forall m.
  ConstructorDef
  { con_name :: DataConName,
    con_arguments :: Telescope m n
  }

unitDef :: DataDef
unitDef =
  Data
    { data_name = "Unit",
      data_params = None,
      data_sort = Star,
      data_constructors = [unitCon]
    }

unitCon :: ConstructorDef N0
unitCon =
  ConstructorDef
    { con_name = "()",
      con_arguments = None
    }

boolDef :: DataDef
boolDef =
  Data
    { data_name = "Bool",
      data_params = None,
      data_sort = Star,
      data_constructors = [boolCon False, boolCon True]
    }

boolCon :: Bool -> ConstructorDef N0
boolCon b = ConstructorDef {con_name = show b, con_arguments = None}

eitherDef :: DataDef
eitherDef =
  Data
    { data_name = "Either",
      data_params = None :<> Const Star :<> Const Star,
      data_sort = Star,
      data_constructors = [eitherLeft, eitherRight]
    }

eitherLeft :: ConstructorDef N2
eitherLeft =
  ConstructorDef
    { con_name = "Left",
      con_arguments = None :<> Var f0
    }

eitherRight :: ConstructorDef N2
eitherRight =
  ConstructorDef
    { con_name = "Right",
      con_arguments = None :<> Var f1
    }

prelude :: [DataDef]
prelude = [unitDef, boolDef, eitherDef]
