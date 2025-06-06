-- | An implementation of System F as a (quasi) Pure Type System.
module PureSystemF where

import Control.Monad (unless)
import Control.Monad.Except (Except (..), MonadError (..), runExcept)
import Data.Fin (f0, f1, f2)
import Data.Vec ((!))
import Data.Vec qualified as Vec
import Rebound
import Rebound.Bind.Local
import Rebound.MonadNamed qualified as Scoped
import Rebound.MonadScoped (MonadScopedReader (..), ScopedReader, ScopedReaderT (..), asksS, runScopedReader)
import Rebound.MonadScoped qualified as Scoped
import Text.Read (Lexeme (String))

-- | We represent both terms and types using one single
-- syntactic class. We use one single constructor for variables,
-- regardless of whether they stand for a term or a
-- variable. We also use an additional constructor, 'Kind',
-- which is used to represent the type of types.
data Exp (n :: Nat) where
  Var :: Fin n -> Exp n
  Kind :: Exp n
  -- Types
  TAll :: Bind Ty Ty n -> Ty n
  TArr :: Ty n -> Ty n -> Ty n
  -- Terms
  Abs :: Ty n -> Bind Exp Exp n -> Exp n
  App :: Exp n -> Exp n -> Exp n
  TAbs :: Bind Ty Exp n -> Exp n
  TApp :: Exp n -> Ty n -> Exp n
  deriving (Eq)

-- | An alias used for readability.
type Ty = Exp

--------------------------------------------------------------------------------
--- Instances required by Rebound
--------------------------------------------------------------------------------

instance Eq (Bind Exp Exp n) where
  l == r = getBody l == getBody r

instance SubstVar Exp where
  var = Var

instance Subst Exp Exp where
  applyE :: forall n m. Env Exp n m -> Exp n -> Exp m
  applyE env t = case t of
    Var x -> applyEnv env x
    Kind -> Kind
    TAll bnd -> TAll (r bnd)
    TArr t1 t2 -> TArr (r t1) (r t2)
    Abs ty bnd -> Abs (r ty) (r bnd)
    App t1 t2 -> App (r t1) (r t2)
    TAbs bnd -> TAbs (r bnd)
    TApp t1 t2 -> TApp (r t1) (r t2)
    where
      r :: forall t. (Subst Exp t) => t n -> t m
      r = applyE env

-- We will be needing strengthening in the type-checker;
-- more on that later.
instance Strengthen Exp where
  strengthenRec ::
    forall k m n.
    SNat k ->
    SNat m ->
    SNat n ->
    Exp (k + (m + n)) ->
    Maybe (Exp (k + n))
  strengthenRec k m n t = case t of
    Var x -> Var <$> strengthenRec k m n x
    Kind -> return Kind
    TAll bnd -> TAll <$> r bnd
    TArr t1 t2 -> TArr <$> r t1 <*> r t2
    Abs ty bnd -> Abs <$> r ty <*> r bnd
    App t1 t2 -> App <$> r t1 <*> r t2
    TAbs bnd -> TAbs <$> r bnd
    TApp t1 t2 -> TApp <$> r t1 <*> r t2
    where
      r :: (Strengthen t) => t (k + (m + n)) -> Maybe (t (k + n))
      r = strengthenRec k m n

--------------------------------------------------------------------------------
--- Typechecking
--------------------------------------------------------------------------------

-- | An environment mapping (de Bruijn) variables to
-- a user-defined name and its type.
data TcEnv n = TcEnv
  { names :: Vec n LocalName,
    types :: Ctx Exp n
  }

emptyEnv :: TcEnv Z
emptyEnv = TcEnv {names = Vec.empty, types = zeroE}

-- | Add a new binding to the environment
extendE :: (LocalName, Exp n) -> TcEnv n -> TcEnv (S n)
extendE (n, t) (TcEnv ns ts) =
  TcEnv (n ::: ns) (ts +++ t)

-- | Search for a binding. Lookup cannot fail
-- thanks to extrinsic scoping.
lookupE :: TcEnv n -> Fin n -> (LocalName, Exp n)
lookupE (TcEnv ns ts) i = (ns ! i, applyEnv ts i)

type Error = String

-- | Typechecking monad.
newtype TC n a = TC (ScopedReaderT TcEnv (Except Error) n a)
  deriving (Functor, Applicative, Monad, MonadError Error)

-- Trivial lifting through a newtype.
instance MonadScopedReader TcEnv TC where
  askS = TC askS
  localS f (TC m) = TC (localS f m)

-- | Run the type-checking monad. Returns
-- either the result, or an error.
runTC :: TcEnv n -> TC n a -> Either Error a
runTC env (TC m) = runExcept $ runScopedReaderT m env

-- | Extend the current (latent) scope with a new binding.
push :: LocalName -> Exp n -> TC (S n) a -> TC n a
push n t = Scoped.localS $ extendE (n, t)

-- | Lookup a binding in the (latent) scope.
get :: Fin n -> TC n (LocalName, Exp n)
get i = readerS (`lookupE` i)

-- | Checks that a given type is indeed a (valid) type,
-- by ensuring that its own type is 'Kind'.
ensureType :: (SNatI n) => Ty n -> TC n ()
ensureType Kind = return ()
ensureType ty = do
  k <- inferType ty
  unless (k == Kind) $ throwError "Not a type"

-- | Infer the type of an expression.
inferType :: (SNatI n) => Exp n -> TC n (Ty n)
inferType (Var x) = do
  (_, ty) <- get x
  ensureType ty
  return ty
inferType Kind =
  -- Kind is used internally to represent a well-formed
  -- type, but should not be used otherwise.
  throwError "Cannot type 'Kind'"
-- Types
inferType (TAll bnd) = do
  let (x, t) = unbindl bnd
  push x Kind $ ensureType t
  return Kind
inferType (TArr l r) =
  ensureType l >> ensureType r >> return Kind
-- Terms
inferType (Abs xTy bnd) = do
  let (x, t) = unbindl bnd
  ensureType xTy
  tTy <- push x xTy $ inferType t
  -- Because the type system is not dependent, we cannot
  -- allow 'x' to occur in 'tTy'. Ensuring this and bringing
  -- 'tTy' into the outer scope is done using 'strengthenN'.
  case strengthenN s1 tTy of
    Just tTy' -> return $ TArr xTy tTy'
    Nothing -> throwError "Term variable occurs in type"
inferType (App l r) = do
  lTy <- inferType l
  rTy <- inferType r
  case lTy of
    TArr rTy' retTy -> do
      unless (rTy == rTy') $ throwError "Argument mismatch"
      return retTy
    _ -> throwError "Left hand-side of application is not an arrow"
inferType (TAbs bnd) = do
  let (x, t) = unbindl bnd
  tTy <- push x Kind $ inferType t
  return $ TAll $ bind x tTy
inferType (TApp l r) = do
  lTy <- inferType l
  ensureType r
  case lTy of
    TAll bnd -> return $ instantiate bnd r
    _ -> throwError "Left hand-side is not a forall"

--------------------------------------------------------------------------------
--- (Pretty) Printing
--------------------------------------------------------------------------------

-- | An environment mapping variables to their (user-defined) name.
data PpEnv n = PpEnv
  { ppnames :: Vec n String,
    pplevel :: Int
  }

-- | Pretty-print a term.
pp :: Vec n LocalName -> Exp n -> String
pp s e = runScopedReader (pp' e) (PpEnv {ppnames = fmap name s, pplevel = 0})
  where
    setLevel :: Int -> ScopedReader PpEnv n String -> ScopedReader PpEnv n String
    setLevel newLevel = localS (\e -> e {pplevel = newLevel})

    atLevel :: Int -> ScopedReader PpEnv n String -> ScopedReader PpEnv n String
    atLevel newLevel m = do
      level <- asksS pplevel
      let m' = if level <= newLevel then m else (\s -> "(" ++ s ++ ")") <$> m
      setLevel newLevel m'

    push n = localS (\e -> e {ppnames = n ::: ppnames e})

    pp' :: Exp n -> ScopedReader PpEnv n String
    pp' (Var f) = asksS (\e -> ppnames e ! f)
    pp' Kind = return "Kind"
    pp' (TAll bnd) = atLevel 0 $ do
      let (LocalName x, b) = unbindl bnd
      b' <- push x $ pp' b
      return $ "∀" ++ x ++ ". " ++ b'
    pp' (TArr l r) = atLevel 1 $ do
      l' <- atLevel 2 $ pp' l
      r' <- pp' r
      return $ l' ++ " -> " ++ r'
    pp' (Abs ty bnd) = atLevel 0 $ do
      let (LocalName x, b) = unbindl bnd
      b' <- push x $ pp' b
      return $ "λ" ++ x ++ ". " ++ b'
    pp' (App l r) = atLevel 2 $ do
      l' <- pp' l
      r' <- atLevel 3 $ pp' r
      return $ l' ++ " " ++ r'
    pp' (TAbs bnd) = atLevel 0 $ do
      let (LocalName x, b) = unbindl bnd
      b' <- push x $ pp' b
      return $ "Λ" ++ x ++ ". " ++ b'
    pp' (TApp l r) = atLevel 2 $ do
      l' <- pp' l
      r' <- setLevel 0 $ pp' r
      return $ l' ++ " [" ++ r' ++ "]"

instance Show (Exp Z) where
  show = pp Vec.empty

t0, t1, t2 :: Exp Z
t0 = TAbs (bind (LocalName "X") $ Abs (var f0) (bind (LocalName "x") $ var f0))
-- >>> t0
-- >>> runTC emptyEnv $ inferType t0
-- ΛX. λx. x
-- Right ∀X. X -> X

t1 = TAbs (bind (LocalName "X") $ Abs (TAll (bind (LocalName "Y") $ TArr (var f0) (var f0))) (bind (LocalName "f") $ Abs (var f1) (bind (LocalName "x") $ App (TApp (var f1) (var f2)) (var f0))))
-- >>> t1
-- >>> runTC emptyEnv $ inferType t1
-- ΛX. λf. λx. f [X] x
-- Right ∀X. (∀Y. Y -> Y) -> X -> X

t2 = Abs Kind (bind (LocalName "X") $ Abs (var f0) (bind (LocalName "x") (var f0)))
-- >>> t2
-- >>> runTC emptyEnv $ inferType t2
-- λX. λx. x
-- Left "Term variable occurs in type"

bbn0, bbn1, bbn2 :: Exp Z
bbn0 = TAbs (bind (LocalName "X") $ Abs (TArr (var f0) (var f0)) (bind (LocalName "f") $ Abs (var f1) (bind (LocalName "z") $ (var f0))))
bbn1 = TAbs (bind (LocalName "X") $ Abs (TArr (var f0) (var f0)) (bind (LocalName "f") $ Abs (var f1) (bind (LocalName "z") $ App (var f1) (var f0))))
bbn2 = TAbs (bind (LocalName "X") $ Abs (TArr (var f0) (var f0)) (bind (LocalName "f") $ Abs (var f1) (bind (LocalName "z") $ App (var f1) (App (var f1) (var f0)))))
-- >>> bbn0
-- >>> runTC emptyEnv $ inferType bbn0
-- ΛX. λf. λz. z
-- Right ∀X. (X -> X) -> X -> X

-- >>> bbn1
-- >>> runTC emptyEnv $ inferType bbn1
-- ΛX. λf. λz. f z
-- Right ∀X. (X -> X) -> X -> X

-- >>> bbn2
-- >>> runTC emptyEnv $ inferType bbn2
-- ΛX. λf. λz. f (f z)
-- Right ∀X. (X -> X) -> X -> X
