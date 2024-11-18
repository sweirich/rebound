-- Dependent type system, based on pi-forall (version4)
-- This is an advanced usage of the binding library and 
-- includes dependent pattern matching

{-# LANGUAGE UndecidableInstances #-}
module PiForall where

import Lib
import qualified Fin
import qualified Vec
import AutoEnv

import qualified Data.Maybe as Maybe
import Control.Monad(zipWithM_, guard)
import Text.ParserCombinators.Parsec.Pos (SourcePos, newPos)
import Control.Monad.Except ( MonadError(..), ExceptT, runExceptT )

data Const = Star | TyUnit | TmUnit | TyBool | TmBool Bool 
   deriving (Eq)

-- In this version, `Match` introduces a Pi type and generalizes lambda. 
-- If the pattern is a single variable, or an annotated variable, 
-- then the term is just a function. But the pattern could be more 
-- than that, supporting a general form of pattern matching.
data Exp (n :: Nat) =
      Const Const
    | Pi    (Exp n) (Bind Exp Exp n)
    | Var   (Fin n) 
    | Match [Branch n]
    | App   (Exp n) (Exp n)
    | Sigma (Exp n) (Bind Exp Exp n)
    | Pair  (Exp n) (Exp n)
    | Annot (Exp n) (Exp n)

-- Patterns with embedded type annotations
-- p is the number of variables bound by the pattern
-- n is the number of free variables in type annotations in the pattern
-- This definitions support telescopes: variables bound earlier in the pattern 
-- can appear later.  For example,
--  (x,(y :: x)) : exists x:*.x
pat0 :: Pat N2 N0
pat0 = PPair PVar (PAnnot PVar (Var f0))

data Pat (p :: Nat) (n :: Nat) where
      PConst :: Const -> Pat N0 n
      PVar   :: Pat N1 n
      PApp   :: (Pat p1 n) -> (Pat p2 (Plus p1 n)) -> Pat (Plus p1 p2) n
      PPair  :: (Pat p1 n) -> (Pat p2 (Plus p1 n)) -> Pat (Plus p1 p2) n
      PAnnot :: (Pat p n)  -> (Exp n)    -> Pat p n

-- A single branch in a match expression. Binds a pattern 
-- with expression variables, with an expression body
data Branch (n :: Nat) = 
    forall p. Branch (PatBind Exp Exp (Pat p) n)

-------------------------------------------------------
-- * definitions for pattern matching 

-- we can count the number of variables bound in the pattern
-- (though we probably already know it)
instance Sized (Pat p) where
    type Size (Pat p) = p
    size :: Pat p n -> SNat p
    size (PConst i) = s0
    size PVar = s1
    size (PApp p1 p2) = sPlus (size p1) (size p2)
    size (PPair p1 p2) = sPlus (size p1) (size p2)
    size (PAnnot p _) = size p


-- | Compare a pattern with an expression, potentially 
-- producing a substitution for all of the variables
-- bound in the pattern
patternMatch :: forall p n. Pat p n -> Exp n -> Maybe (Env Exp p n)
patternMatch PVar e = Just $ oneE e
patternMatch (PApp (p1 :: Pat p1 n) (p2 :: Pat p2 (Plus p1 n))) (App e1 e2)  = do
    env1 <- patternMatch p1 e1
    env2 <- patternMatch (applyE env1 p2) e2
    withSNat (size p1) $ return (env1 .++ env2)
patternMatch (PConst s1) (Const s2) = 
    if s1 == s2 then Just zeroE else Nothing
patternMatch (PPair p1 p2) (Pair e1 e2) = do
    env1 <- patternMatch p1 e1
    env2 <- patternMatch (applyE env1 p2) e2
    withSNat (size p1) $ return (env1 .++ env2)   
patternMatch (PAnnot p _) e = patternMatch p e
patternMatch p (Annot e _)  = patternMatch p e
patternMatch _ _ = Nothing

findBranch :: forall n. Exp n -> [Branch n] -> Maybe (Exp n)
findBranch e [] = Nothing
findBranch e (Branch (bnd :: PatBind Exp Exp (Pat p) n) : brs) = 
    case patternMatch (getPat bnd) e of
        Just r -> Just $ instantiatePat bnd r
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
    applyE r (PApp p1 p2) = PApp (applyE r p1) (applyE r p2)
    applyE r (PPair p1 p2) = PPair (applyE r p1) (applyE r p2)
    applyE r (PAnnot p t) = PAnnot (applyE r p) (applyE r t)

instance Subst Exp Branch where
    applyE :: forall n m. Env Exp n m -> Branch n -> Branch m
    applyE r (Branch (b :: PatBind Exp Exp (Pat p) n)) = Branch (applyE r b)

----------------------------------------------
-- Free variable calculation

t00 :: Exp N2
t00 = App (Var f0) (Var f0)

t01 :: Exp N2
t01 = App (Var f0) (Var f1)

-- Does a variable appear free in a term?

class FV (t :: Nat -> Type) where
    appearsFree :: Fin n -> t n -> Bool

-- >>> appearsFree f0 t00
-- True

-- >>> appearsFree f1 t00
-- False

instance FV Exp where
    -- appearsFree :: Fin n -> Exp' n -> Bool
    appearsFree n (Var x) = n == x
    appearsFree n (Const c) = False
    appearsFree n (Pi a b) = appearsFree n a || appearsFree (FS n) (unbind b)
    -- appearsFree n (Lam Nothing b) = appearsFree (FS n) (unbind b)
    -- appearsFree n (Lam (Just a) b) = appearsFree n a || appearsFree (FS n) (unbind b)
    appearsFree n (App a b) = appearsFree n a || appearsFree n b
    appearsFree n (Sigma a b) = appearsFree n a || appearsFree (FS n) (unbind b)
    appearsFree n (Pair a b) = appearsFree n a || appearsFree n b
    appearsFree n (Match b) = any (appearsFree n) b
    appearsFree n (Annot a t) = appearsFree n a || appearsFree n t

instance FV Branch where
    appearsFree n (Branch bnd) = appearsFree n bnd

instance FV (Pat p) where
    appearsFree n PVar  = False
    appearsFree n (PConst _) = False
    appearsFree n (PApp p1 p2) = appearsFree n p1 || appearsFree n p2
    appearsFree n (PPair p1 p2) = appearsFree n p1 || appearsFree n p2
    appearsFree n (PAnnot p t) = appearsFree n p || appearsFree n t

instance (Subst v v, Subst v c, 
            Sized p, FV p, FV c) => FV (PatBind v c p) where
    appearsFree n b = 
        let pat = getPat b in
        appearsFree n pat
          || appearsFree (shiftN (size pat) n) (unPatBind b)

-- instance FV Exp where
--    appearsFree n (Pos _ e) = appearsFree n e

-- >>> :t weaken' s1 t00
-- weaken' s1 t00 :: Exp ('S ('S N1))

-- >>> weaken' s1 t00
-- 0 0

weaken' :: SNat m -> Exp n -> Exp (Plus m n)
weaken' m = applyE @Exp (weakenE' m)

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
    strengthen' m n PVar = pure PVar
    strengthen' m n (PConst c) = pure (PConst c)
    strengthen' m n (PApp p1 p2) = PApp <$> strengthen' m n p1 
                                        <*> strengthen' m n p2
    strengthen' m n (PPair p1 p2) = PPair <$> strengthen' m n p1 
                                          <*> strengthen' m n p2
    strengthen' m n (PAnnot p1 e2) = PAnnot <$> strengthen' m n p1 
                                        <*> strengthen' m n e2
instance Strengthen Branch where
    strengthen' m n (Branch bnd) = Branch <$> strengthen' m n bnd

----------------------------------------------
-- Examples

star :: Exp n
star = Const Star

lam :: Maybe (Exp n) -> Exp (S n) ->Exp n
lam Nothing b = Match [Branch (patBind PVar b)]
lam (Just t) b = Match [Branch (patBind (PAnnot PVar t) b)]

-- The identity function "λ x. x". With de Bruijn indices
-- we write it as "λ. 0"
t0 :: Exp Z 
t0 = lam (Just star) (Var f0)

-- A larger term "λ x. λy. x (λ z. z z)"
-- λ. λ. 1 (λ. 0 0)
t1 :: Exp Z
t1 = lam (Just star)
       (lam (Just star) 
          (Var f1 `App` lam (Just star) (Var f0 `App` Var f0)))

-- To show lambda terms, we can write a simple recursive instance of 
-- Haskell's `Show` type class. In the case of a binder, we use the `unbind` 
-- operation to access the body of the lambda expression.

-- >>> t0
-- Prelude.undefined

-- >>> t1
-- λ. λ. 1 (λ. 0 0)

-- Polymorphic identity function and its type

tyid = Pi star (bind (Pi (Var f0) (bind (Var f1))))
tmid = lam (Just star) (lam (Just (Var f0)) (Var f0))

-- >>> tyid
-- Pi *.(0 -> 1)

-- >>> tmid
-- λ. λ. 0

instance Show Const where
    show Star = "*"
    show TyUnit = "Unit"
    show TmUnit = "()"
    show TyBool = "Bool"
    show (TmBool b) = show b


instance Show (Exp n) where
    showsPrec :: Int -> Exp n -> String -> String
    showsPrec _ (Const c) = showString (show c)
    showsPrec d (Pi a b)
      | appearsFree FZ (unbind b) = 
        showParen (d > 10) $
          showString "Pi " .
          shows a .
          showString ". " .
          shows (unbind b)
      | otherwise = 
        showParen (d > 10) $
          showsPrec 11 a .
          showString " -> " .
          showsPrec 10 (unbind b)
    showsPrec d (Sigma a b)
      | appearsFree FZ (unbind b) = 
        showParen (d > 10) $
          showString "Sigma " .
          shows a .
          showString ". " .
          shows (unbind b)
      | otherwise = 
        showParen (d > 10) $
          showsPrec 11 a .
          showString " * " .
          showsPrec 10 (unbind b)
    showsPrec _ (Var x) = shows (toInt x)
    showsPrec d (App e1 e2) = showParen (d > 0) $
                              showsPrec 10 e1 . 
                              showString " " .
                              showsPrec 11 e2
    --showsPrec d (Lam t b) = showParen (d > 10) $ 
    --                         showString "λ. " .
    --                         shows (unbind b) 
    showsPrec d (Pair e1 e2) = showParen (d > 0) $
                              showsPrec 10 e1 . 
                              showString ", " .
                              showsPrec 11 e2
    showsPrec d (Match b) = showParen (d > 10) $ 
                              showString "match" .
                              showsPrec 10 b 
    showsPrec d (Annot a t) = showParen (d > 10) $ 
        showsPrec 10 a . 
        showString " : " .
        showsPrec 10 t

instance Show (Branch b) where
    showsPrec d (Branch b) = undefined


testEquality2 :: Pat m1 n -> Pat m2 n -> Maybe (m1 :~: m2)
testEquality2 PVar PVar = Just Refl
testEquality2 (PApp p1 p2) (PApp p1' p2') = do 
        Refl <- testEquality2 p1 p1'
        Refl <- testEquality2 p2 p2'
        return Refl
testEquality2 (PPair p1 p2) (PPair p1' p2') = do 
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
    (Branch (p1 :: PatBind Exp Exp (Pat m1) n)) ==
      (Branch (p2 :: PatBind Exp Exp (Pat m2) n)) =  
        case testEquality (size (getPat p1) :: SNat m1) 
                          (size (getPat p2) :: SNat m2) of
            Just Refl -> p1 == p2
            Nothing -> False

-- To compare pattern binders, we need to unbind, but also 
-- make sure that the patterns are equal
instance (Eq (Exp n)) => Eq (PatBind Exp Exp (Pat m) n) where
        b1 == b2 =
            Maybe.isJust (testEquality2 (getPat b1) (getPat b2))
             && unPatBind b1 == unPatBind b2

-- To compare binders, we only need to `unbind` them
instance Eq (Exp n) => Eq (Bind Exp Exp n) where
        b1 == b2 = unbind b1 == unbind b2

instance Eq (Exp n) => Eq (Bind2 Exp Exp n) where
        b1 == b2 = unbind2 b1 == unbind2 b2


-- With the instance above the derivable equality instance
-- is alpha-equivalence
deriving instance (Eq (Exp n))



--------------------------------------------------------

{- We can write the usual operations for evaluating 
   lambda terms to values -}

-- big-step evaluation



-- >>> eval t1
-- λ. λ. 1 (λ. 0 0)

-- >>> eval (t1 `App` t0)
-- λ. λ. 0 (λ. 0 0)

eval :: Exp n -> Exp n
eval (Var x) = Var x
eval (Match b) = Match b
eval (App e1 e2) =
    let v = eval e2 in
    case eval e1 of
        Match b -> case findBranch v b of
                Just e -> eval e
                Nothing -> error "pattern match failure"
        t -> App t v
eval (Const c) = Const c
eval (Pi a b) = Pi a b
eval (Sigma a b) = Sigma a b
eval (Annot a t) = eval a
eval (Pair a b) = Pair a b
{-
eval (Split a b) = 
    case eval a of
      Pair a1 a2 _ -> 
        eval (instantiate2 b (eval a1) (eval a2))
      t -> Split t b
      -}
-- small-step evaluation

-- >>> step (t1 `App` t0)
-- Just (λ. λ. 0 (λ. 0 0))

step :: Exp n -> Maybe (Exp n)
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

eval' :: Exp n -> Exp n
eval' e 
 | Just e' <- step e = eval' e'
 | otherwise = e


----------------------------------------------------------------
data Err where
    NotEqual :: Exp n -> Exp n -> Err
    PiExpected :: Exp n -> Err
    SigmaExpected :: Exp n -> Err
    VarEscapes :: Exp n -> Err
    PatternMismatch :: Pat p1 n1 -> Pat p2 n2 -> Err
    PatternTypeMismatch :: Pat p1 n1 -> Exp n1 -> Err
    AnnotationNeeded :: Exp n -> Err

-- find the head form
whnf :: Exp n -> Exp n
whnf (App a1 a2) = case whnf a1 of 
                    Match bs -> case findBranch (eval a2) bs of
                        Just b -> whnf b
                        Nothing -> App (Match bs) a2
                    t -> App t a2
whnf (Annot a t) = whnf a
whnf a = a

equate :: MonadError Err m => Exp n -> Exp n -> m ()
equate t1 t2 = do 
  let n1 = whnf t1
      n2 = whnf t2  
  equateWHNF n1 n2

equateBranch :: (MonadError Err m) => Branch n -> Branch n -> m ()
equateBranch (Branch (b1 :: PatBind Exp Exp (Pat p1) n)) (Branch (b2 :: PatBind Exp Exp (Pat p2) n)) = 
    let s1 = size (getPat b1)
        s2 = size (getPat b2)
        e1 = unPatBind b1 
        e2 = unPatBind b2 in
    case testEquality s1 s2 of
        Just Refl -> equate e1 e2 
        Nothing -> throwError (PatternMismatch (getPat b1) (getPat b2))


equateWHNF :: MonadError Err m => Exp n -> Exp n -> m () 
equateWHNF n1 n2 = 
  case ( n1 , n2 ) of
    (Const c1, Const c2) | c1 == c2 -> pure ()
    (Var x, Var y) | x == y -> pure ()
    (Match b1, Match b2) -> 
        zipWithM_ equateBranch b1 b2
    (App a1 a2, App b1 b2) -> do
        equateWHNF a1 b1 
        equate a2 b2
    (Pi tyA1 b1, Pi tyA2 b2) -> do
        equate tyA1 tyA2 
        unbindWith b1 (\ r1 t1 -> 
            unbindWith b2 (\ r2 t2 ->
                equate (applyE (up r1) t1) (applyE (up r2) t2)))
    (Sigma tyA1 b1, Sigma tyA2 b2) -> do
        equate tyA1 tyA2
        equate (unbind b1) (unbind b2)
    (_, _) -> throwError (NotEqual n1 n2)


----------------------------------------------------------------


-- convert a pattern to an expression
-- the expression should check in a scope where all of the variables
-- have been added to the context. 
-- Any type annotations in the pattern must also have their variables
-- weakened 

-- >>> pat2Exp (PApp PVar (PAnnot PVar (Var f0)))
-- 1 (1 : 1)
-- NO! should be:    1 (2 : 0)

pat2Exp :: forall p n. SNat n -> Pat p n -> Exp (Plus p n)
pat2Exp n PVar = Var (largest n)
pat2Exp n (PConst c) = Const c
pat2Exp n (PPair (p1 :: Pat p1 n) (p2 :: Pat p2 n)) = undefined
{-
    let e1 = pat2Exp p1
        e1' = applyE (shiftRE @Exp @p1 @p2 @n (size p2)) e1
        e2 = pat2Exp p2
        e2' = applyE (shiftLE @Exp @p1 @p2 @n (size p1)) e2
    in App e1' e2'
    -}
pat2Exp n (PApp (p1 :: Pat p1 n) (p2 :: Pat p2 n)) = undefined
{-
    let e1 = pat2Exp p1
        e1' = applyE (shiftRE @Exp @p1 @p2 @n (size p2)) e1
        e2 = pat2Exp p2
        e2' = applyE (shiftLE @Exp @p1 @p2 @n (size p1)) e2
    in App e1' e2'
    -}
pat2Exp n (PAnnot p1 t) = 
    let e1 = pat2Exp n p1
    in Annot e1 (applyE (weakenE' @_ @Exp (size p1)) t)

inferConst :: Const -> Exp n
inferConst Star = Const Star
inferConst TmUnit = Const TyUnit
inferConst TyUnit = Const Star
inferConst (TmBool _) = Const TyBool
inferConst TyBool = Const Star

-- type check a pattern and produce a typing context, plus expression 
-- form of the pattern (for dependent pattern matching)
checkPattern :: (MonadError Err m, SNatI n) => 
  Ctx Exp n -> Pat p n -> Exp n -> 
     m (Ctx Exp (Plus p n), Exp (Plus p n))
{-
checkPattern = undefined
checkPattern PVar a = pure $ oneE a
checkPattern (PConst c) ty 
  | inferConst c == ty = pure zeroE 
checkPattern (PPair p1 p2) (Sigma tyA tyB) = do
  env1 <- checkPattern p1 tyA 
  let e1 = pat2Exp snat p1
  env2 <- checkPattern p2 undefined -- (instantiate tyB e1)
  withSNat (size p1) $ return (env1 .++ env2)
checkPattern (PApp p1 p2) ty = undefined
checkPattern (PAnnot p ty1) ty = 
    checkPattern p ty1
checkPattern p ty = throwError (PatternTypeMismatch p ty)
-}

checkBranch :: forall m n. (MonadError Err m, SNatI n) => 
    Ctx Exp n -> Exp n -> Branch n ->  m ()
checkBranch g (Pi tyA tyB)  (Branch bnd) = do
    (g', a) <- checkPattern g (getPat bnd) tyA 
    let sp = size (getPat bnd)
    let tyB' = applyE (weakenE' @_ @Exp sp) tyB
    let tyB'' = whnf (instantiate tyB' a)
    let body = unPatBind bnd
    withSNat (sPlus sp (snat @n)) $ checkType g' body tyB''
checkBranch g t e = throwError (PiExpected t)

-- should only check with a type in whnf
checkType :: forall n m. (MonadError Err m, SNatI n) => 
   Ctx Exp n -> Exp n -> Exp n -> m ()
checkType g (Pair a b) ty = do 
    tyA <- inferType g a 
    tyB <- inferType g b 
    case ty of 
        (Sigma tyA tyB) -> do
            checkType g a tyA
            checkType g b (instantiate tyB a)
        _ -> throwError (SigmaExpected ty)
checkType g (Match bs) ty = do
    mapM_ (checkBranch g ty) bs
checkType g e t1 = do
    t2 <- inferType g e 
    equate (whnf t2) t1

inferType :: forall n m. (MonadError Err m, SNatI n) => 
   Ctx Exp n -> Exp n -> m (Exp n)
inferType g (Var x) = pure (applyEnv g x)
inferType g (Const c) = pure (inferConst c)
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
        t -> throwError (PiExpected t)
inferType g (Sigma a b) = do
    checkType g a (Const Star)
    checkType (g +++ a) (unbind b) (Const Star)
    pure (Const Star)
inferType g a = 
    throwError (AnnotationNeeded a)

emptyE :: Ctx Exp Z 
emptyE = Env $ \case

-- >>> inferType emptyE tmid
-- Just (Pi *. 0 -> 1)

-- >>> inferType emptyE (App tmid tyid)
-- Just ((Pi *. 0 -> 1) -> Pi *. 0 -> 1)
