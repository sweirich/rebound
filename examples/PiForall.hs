-- A dependent type system, based on pi-forall (version4)
-- This is an advanced usage of the binding library and 
-- includes nested dependent pattern matching. It doesn't 
-- type check yet.

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
module PiForall where

import Lib
import qualified Fin
import qualified Vec
import AutoEnv

import qualified Data.Maybe as Maybe
import Control.Monad(zipWithM_, guard)
import Text.ParserCombinators.Parsec.Pos (SourcePos, newPos)
import Control.Monad.Except ( MonadError(..), ExceptT, runExceptT )

import Debug.Trace

data Const = Star | TyUnit | TmUnit | TyBool | TmBool Bool 
   deriving (Eq)

-- In system, `Match` introduces a Pi type and generalizes lambda. 
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
-- can appear later.  For example, a type paired with a term of that type
-- can look like this (and have a Sigma type)
--   (x,(y :: x)) : Sigma x:*.x
pat0 :: Pat N2 N0
pat0 = PPair PVar (PAnnot PVar (Var f0))

-- The nat `p` is the number of variables bound in the pattern
-- The nat `n` is the scope for expressions that appear in annotations
-- In the App/Pair patterns, we increase the scope so that variables 
-- bound in the left subterm can be referred to in the right subterm.
data Pat (p :: Nat) (n :: Nat) where
  PConst :: Const -> Pat N0 n
  PVar   :: Pat N1 n
  PApp   :: (Pat p1 n) -> (Pat p2 (Plus p1 n)) -> Pat (Plus p2 p1) n
  PPair  :: (Pat p1 n) -> (Pat p2 (Plus p1 n)) -> Pat (Plus p2 p1) n
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
    size (PApp p1 p2) = sPlus (size p2) (size p1)
    size (PPair p1 p2) = sPlus (size p2) (size p1)
    size (PAnnot p _) = size p

tm0 :: Exp Z
tm0 = Pair (Const TyBool) (Const (TmBool True))




-- >>> patternMatch pat0 tm0
-- Just [Bool,True]

-- TODO: better name for this function? 
append :: forall n p e. SubstVar e => SNat p -> Env e p n -> Env e (Plus p n) n
append p (Env f) = Env $ \(x :: Fin (Plus p n)) -> 
    case checkBound p x of
         Left y -> f y
         Right y -> var y


-- | Compare a pattern with an expression, potentially 
-- producing a substitution for all of the variables
-- bound in the pattern
patternMatch :: forall p n. SNatI n => Pat p n -> Exp n -> Maybe (Env Exp p n)
patternMatch PVar e = Just $ oneE e
patternMatch (PApp (p1 :: Pat p1 n) (p2 :: Pat p2 (Plus p1 n))) (App e1 e2)  = do
    -- env1 :: Env Exp p1 n
    env1 <- patternMatch p1 e1
    let r :: Env Exp (Plus p1 n) n
        r = append (size p1) env1
    let p2' :: Pat p2 n
        p2' = applyE r p2
    env2 <- patternMatch p2' e2
    withSNat (size p2) $ return (env2 .++ env1)
patternMatch (PConst s1) (Const s2) = 
    if s1 == s2 then Just zeroE else Nothing
patternMatch (PPair p1 p2) (Pair e1 e2) = do
    env1 <- patternMatch p1 e1
    let r = append (size p1) env1
    env2 <- patternMatch (applyE r p2) e2
    withSNat (size p2) $ return (env2 .++ env1)   
patternMatch (PAnnot p _) e = patternMatch p e
patternMatch p (Annot e _)  = patternMatch p e
patternMatch _ _ = Nothing

findBranch :: forall n. SNatI n => Exp n -> [Branch n] -> Maybe (Exp n)
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
    applyE r (PApp p1 p2) = PApp (applyE r p1) (applyE (upN (size p1) r) p2)
    applyE r (PPair p1 p2) = PPair (applyE r p1) (applyE (upN (size p1) r) p2)
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
    appearsFree n (Var x) = n == x
    appearsFree n (Const c) = False
    appearsFree n (Pi a b) = appearsFree n a || appearsFree (FS n) (unbind b)
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
    appearsFree n (PApp p1 p2) = appearsFree n p1 
        || appearsFree (shiftN (size p1) n) p2
    appearsFree n (PPair p1 p2) = appearsFree n p1 
        || appearsFree (shiftN (size p1) n) p2
    appearsFree n (PAnnot p t) = appearsFree n p 
        || appearsFree n t

instance (Subst v v, Subst v c, 
            Sized p, FV p, FV c) => FV (PatBind v c p) where
    appearsFree n b = 
        let pat = getPat b in
        appearsFree n pat
          || appearsFree (shiftN (size pat) n) (unPatBind b)

----------------------------------------------
-- weakening 

-- >>> :t weaken' s1 t00
-- weaken' s1 t00 :: Exp ('S ('S N1))

-- >>> weaken' s1 t00
-- 0 0

weaken' :: SNat m -> Exp n -> Exp (Plus m n)
weaken' m = applyE @Exp (weakenE' m)

----------------------------------------------
-- strengthening


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
    strengthen' m n (PApp (p1 :: Pat p1 n1) p2) = 
        case axiomM @m @p1 @n of
            Refl -> 
                     PApp <$> strengthen' m n p1 
                          <*> strengthen' m (sPlus (size p1) n) p2
    strengthen' m n (PPair (p1 :: Pat p1 n1) p2) = 
        case axiomM @m @p1 @n of
            Refl -> PPair <$> strengthen' m n p1 
                                        <*> strengthen' m (sPlus (size p1) n) p2
    strengthen' m n (PAnnot p1 e2) = PAnnot <$> strengthen' m n p1 
                                        <*> strengthen' m n e2
instance Strengthen Branch where
    strengthen' m n (Branch bnd) = Branch <$> strengthen' m n bnd

----------------------------------------------
-- Examples

star :: Exp n
star = Const Star

-- No annotation on the binder
lam :: Exp (S n) ->Exp n
lam b = Match [Branch (patBind PVar b)]

-- Annotation on the binder
alam :: Exp n -> Exp (S n) -> Exp n
alam t b = Match [Branch (patBind (PAnnot PVar t) b)]

-- The identity function "λ x. x". With de Bruijn indices
-- we write it as "λ. 0", though with `Match` it looks a bit different
t0 :: Exp Z 
t0 = lam (Var f0)

-- A larger term "λ x. λy. x (λ z. z z)"
-- λ. λ. 1 (λ. 0 0)
t1 :: Exp Z
t1 = lam 
       (lam 
          (Var f1 `App` lam (Var f0 `App` Var f0)))

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
-- * Show instances
--------------------------------------------------------

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
    showsPrec d (Pair e1 e2) = showParen (d > 0) $
                              showsPrec 10 e1 . 
                              showString ", " .
                              showsPrec 11 e2
    showsPrec d (Match [b]) = showParen (d > 10) $ 
                              showString "λ" .
                              showsPrec 10 b 
    showsPrec d (Match b) = showParen (d > 10) $ 
                              showString "match" .
                              showsPrec 10 b 
    showsPrec d (Annot a t) = showParen (d > 10) $ 
        showsPrec 10 a . 
        showString " : " .
        showsPrec 10 t

instance Show (Branch b) where
    showsPrec d (Branch b) =
        showsPrec 10 (getPat b) . 
        showString ". " .
        showsPrec 11 (unPatBind b)

instance Show (Pat p n) where
    showsPrec d PVar = showString "_"
    showsPrec d (PConst c) = showsPrec d c
    showsPrec d (PApp e1 e2) = showParen (d > 0) $
                              showsPrec 10 e1 . 
                              showString " " .
                              showsPrec 11 e2
    showsPrec d (PPair e1 e2) = showParen (d > 0) $
                              showsPrec 10 e1 . 
                              showString ", " .
                              showsPrec 11 e2 
    showsPrec d (PAnnot e1 e2) = showParen (d > 0) $ 
                              showsPrec 10 e1 . 
                              showString " : " .
                              showsPrec 11 e2


--------------------------------------------------------
-- * Alpha equivalence
--------------------------------------------------------


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

eval :: SNatI n => Exp n -> Exp n
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

-- small-step evaluation

-- >>> step (t1 `App` t0)
-- Just (λ_. (λ_. 0 (λ_. (0 0))))

step :: SNatI n => Exp n -> Maybe (Exp n)
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

eval' :: SNatI n => Exp n -> Exp n
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
      
deriving instance (Show Err)

-- find the head form
whnf :: SNatI n => Exp n -> Exp n
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

equateBranch :: forall m n. (MonadError Err m, SNatI n) => Branch n -> Branch n -> m ()
equateBranch (Branch (b1 :: PatBind Exp Exp (Pat p1) n)) (Branch (b2 :: PatBind Exp Exp (Pat p2) n)) = 
    let s1 = size (getPat b1)
        s2 = size (getPat b2)
        e1 = unPatBind b1 
        e2 = unPatBind b2 in
    case testEquality s1 s2 of
        Just Refl -> 
            withSNat (sPlus (size (getPat b1)) (snat:: SNat n)) $ 
               equate e1 e2 
        Nothing -> throwError (PatternMismatch (getPat b1) (getPat b2))


equateWHNF :: (SNatI n, MonadError Err m) => Exp n -> Exp n -> m () 
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
        equate (unbind b1) (unbind b2)
    (Sigma tyA1 b1, Sigma tyA2 b2) -> do
        equate tyA1 tyA2
        equate (unbind b1) (unbind b2)
    (_, _) -> throwError (NotEqual n1 n2)


----------------------------------------------------------------
-- * Type checking 
----------------------------------------------------------------

-- | infer the type of a constant term
inferConst :: Const -> Exp n
inferConst Star = Const Star
inferConst TmUnit = Const TyUnit
inferConst TyUnit = Const Star
inferConst (TmBool _) = Const TyBool
inferConst TyBool = Const Star

inferPattern :: (MonadError Err m, SNatI n) => 
    Ctx Exp n ->      -- input context
    Pat p n ->        -- pattern to check
     m (Ctx Exp (Plus p n), Exp (Plus p n), Exp n)
inferPattern g (PConst c) = 
    pure (g, Const c, inferConst c)
inferPattern g (PAnnot p ty) = do
    (g', e) <- checkPattern g p ty
    pure (g', e, ty)
inferPattern g p = throwError (AnnotationNeededPat p) 

-- | type check a pattern and produce an extended typing context, 
-- plus expression form of the pattern (for dependent pattern matching)
checkPattern :: forall m n p. (MonadError Err m, SNatI n) => 
    Ctx Exp n ->      -- input context
    Pat p n ->        -- pattern to check
    Exp n ->          -- expected type of pattern (should be in whnf)
     m (Ctx Exp (Plus p n), Exp (Plus p n))
checkPattern g PVar a = do
    pure (g +++ a, var f0)
checkPattern g (PPair (p1 :: Pat p1 n) (p2 :: Pat p2 (Plus p1 n))) (Sigma tyA tyB) = 
  case axiomAssoc @p2 @p1 @n of 
    Refl ->
        let p = size p1 in
        withSNat (sPlus p (snat @n)) $ do
            (g', e1) <- checkPattern g p1 tyA
            let tyB' = applyE (weakenE' @_ @Exp p) tyB
            let tyB'' = whnf (instantiate tyB' e1)
            (g'', e2) <- checkPattern g' p2 tyB''
            let e1' = applyE (weakenE' @_ @Exp (size p2)) e1
            return (g'', Pair e1' e2) 
checkPattern g (PApp (p1 :: Pat p1 n) (p2 :: Pat p2 (Plus p1 n))) ty = 
    case axiomAssoc @p2 @p1 @n of 
    Refl ->
        let p = size p1 in
        withSNat (sPlus p (snat @n)) $ do
            (g', e1, ty) <- inferPattern g p1
            case whnf ty of 
               Pi tyA tyB -> do
                let tyA' = applyE (weakenE' @_ @Exp p) tyA
                (g'', e2) <- checkPattern g' p2 tyA'
                let e1' = applyE (weakenE' @_ @Exp (size p2)) e1
                let tyB'' = whnf (instantiate (applyE (weakenE' @_ @Exp p) tyB) e1)
                equate tyB'' (weaken' p ty)
                return (g'', App e1' e2) 
               _ -> throwError (PiExpectedPat p1)
checkPattern g p ty = do
  (g', e, ty') <- inferPattern g p 
  equate ty ty'
  return (g', e)

-- >>> instantiate (bind (Var f1)) (Var f0)
-- 0
-- >>> applyE (oneE (Var f0) :: Env Exp N2 N1) ((Var f1) :: Exp N2)
-- Couldn't match type 'Z with 'S N0
-- Expected: Env Exp N2 N1
--   Actual: Env Exp ('S 'Z) N1
-- In the first argument of `applyE', namely
--   `(oneE (Var f0) :: Env Exp N2 N1)'
-- In the expression:
--   applyE (oneE (Var f0) :: Env Exp N2 N1) ((Var f1) :: Exp N2)
-- In an equation for `it_axvSI':
--     it_axvSI
--       = applyE (oneE (Var f0) :: Env Exp N2 N1) ((Var f1) :: Exp N2)

n :: SNat N1
n = snat @N1

p :: SNat N1
p = snat @N1

a :: Exp (Plus N1 N1)
a = Const Star

tyB :: Exp N3
tyB = Var f2

testEnv :: Env Exp N3 N2
testEnv = substWeakenEnv @N1 @N1 n p a

testExp :: Exp N2
testExp = applyE testEnv tyB

-- >>> testEnv
-- [0,*,1]
-- 

-- >>> strengthenOne' (SS SZ) ((FS FZ) :: Fin N2)
-- Nothing

-- >>> :t checkBound
-- checkBound :: SNat p -> Fin (Plus p n) -> Either (Fin p) (Fin n)


weakenFinRight :: forall m n. SNat m -> Fin n -> Fin (Plus n m)
weakenFinRight SZ n = 
    case axiomPlusZ @n of 
        Refl -> n
weakenFinRight (SS (m :: SNat m1)) n = 
    case axiom @n @m1 of 
        Refl -> weaken1Fin (weakenFinRight m n)

substWeakenEnv :: forall p n. SNat n -> SNat p ->
     Exp (Plus p n) -> Env Exp (Plus p (S n)) (Plus p n) 
substWeakenEnv n p a = 
    Env $ \(x :: Fin (Plus p (S n))) -> 
             case checkBound @p @(S n) p x of
                Left pf -> var (weakenFinRight n pf)
                Right pf -> case pf of 
                    FZ -> a
                    FS (f :: Fin n) -> var (shiftN p f)

    




checkBranch :: forall m n. (MonadError Err m, SNatI n) => 
    Ctx Exp n -> Exp n -> Branch n ->  m ()
checkBranch g (Pi tyA tyB) (Branch (bnd :: PatBind Exp Exp (Pat p) n)) = 
   let p = size (getPat bnd) in
   withSNat (sPlus p (snat @n)) $ do
    --traceM $ "***********************************"
    --traceM $ "Scope depth is: " ++ show (snat @n)
    --traceM $ "Checking pattern: " ++ show (getPat bnd)
    --traceM $ "With type: " ++ show tyA
    -- find the extended context and pattern expression
    (g', a) <- checkPattern g (getPat bnd) tyA
    -- double check that a makes sense in extended context
    -- checkType g' a (weaken' p tyA)
    -- traceM $ "New ctx: " ++ show g'
    -- traceM $ "pat2tm: " ++ show a
    let bodyB :: Exp (S n)
        bodyB = unbind tyB
        bodyB' :: Exp (Plus p (S n))
        -- bodyB' = weaken' p bodyB
        bodyB' = applyE (shiftNE @Exp @p @(S n) p) bodyB
    -- traceM $ "unbound: " ++ show bodyB
    -- traceM $ "shifted: " ++ show bodyB'
    let tyB'' :: Exp (Plus p n)
        tyB'' = applyE (substWeakenEnv (snat @n) p a) bodyB'
    -- traceM $ "substWeaken: " ++ show tyB''
    -- weaken the codomain type for the new environment
    --let tyB' = applyE (weakenE' @_ @Exp p) tyB
    -- traceM $ "weakened B: " ++ show (unbind tyB')
    -- need to substitute a for 0 instead of instantiate here!!!
    -- let tyB'' = whnf (instantiate tyB' a)
    -- traceM $ "body type: " ++ show tyB''
    let body = unPatBind bnd
    checkType g' body tyB''
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
    -- traceM $ "Checking exp: " ++ show e
    -- traceM $ "Against type: " ++ show t1
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

-- >>> tmid
-- λ_. (λ_. 0)

-- >>> tyid
-- Pi *. 0 -> 1

-- >>> :t tyid
-- tyid :: Exp n

-- >>> (checkType emptyE tmid tyid :: Either Err ())
-- Left (NotEqual 1 0)

-- >>> inferType emptyE (App tmid tyid)
-- Just ((Pi *. 0 -> 1) -> Pi *. 0 -> 1)


