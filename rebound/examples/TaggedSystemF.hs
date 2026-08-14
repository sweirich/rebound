-- | An implementation of System F as a (quasi) Pure Type System, with a
-- /sorted/ syntax.
--
-- Like "PureSystemF", this uses a single syntactic class and a single scope for
-- both type and term variables. Unlike "PureSystemF", the syntax carries a tag
-- recording whether an expression is a type or a term, so that (for example)
-- the argument of 'TArr' is statically known to be a type.
--
-- The interesting design question is what substitution means here. Because a
-- single scope holds variables of /both/ sorts, and 'Var' may be used at either
-- sort, the variable case of 'applyE' has to produce an expression at whichever
-- sort the occurrence happens to have. A substitution @Env v n m@ carries only
-- one @v@, so it can only do that if every value in its range is legal at every
-- sort. That pins the design down:
--
--   * 'AnyExp' -- values usable at any sort -- is the substitution type for
--     binders that cross sorts ('Abs' and 'TAbs'). Only variables inhabit it,
--     so substitution over the shared scope is a /renaming/.
--
--   * 'Ty' is closed under its own constructors ('Var', 'Kind', 'TAll',
--     'TArr'), so @'Subst' 'Ty' 'Ty'@ is an ordinary substitution. This is the
--     one System F actually needs: instantiating @∀@ at 'TApp'.
--
-- Compared to the untagged version, 'Kind' lives at the 'TTy' tag rather than
-- getting a sort of its own. A separate @Kd@ tag would force 'inferType' to be
-- sort-indexed (the type of a term is a type, but the type of a type is a
-- kind), and would make the context heterogeneous, since it stores 'Kind' as
-- the "type" of every type variable.
module TaggedSystemF where

import Control.Monad (unless)
import Control.Monad.Except (Except, MonadError (..), runExcept)
import Data.Fin (f0, f1, f2)
import Data.Vec ((!))
import Data.Vec qualified as Vec
import Rebound
import Rebound.Bind.Local
import Rebound.MonadScoped (MonadScopedReader (..), ScopedReader, ScopedReaderT (..), asksS, runScopedReader)

--------------------------------------------------------------------------------
--- Syntax
--------------------------------------------------------------------------------

-- | The sort of an expression.
data Tag = TTy | TTm

-- | We represent both terms and types using one single syntactic class, indexed
-- by the sort it belongs to. We use one single constructor for variables,
-- regardless of whether they stand for a type or a term, so 'Var' is
-- polymorphic in the tag. We also use an additional constructor, 'Kind', which
-- is used to represent the type of types.
data Exp (tag :: Tag) (n :: Nat) where
  Var :: Fin n -> Exp tag n
  Kind :: Ty n
  -- Types
  TAll :: Bind Ty Ty n -> Ty n
  TArr :: Ty n -> Ty n -> Ty n
  -- Terms
  Abs :: Ty n -> Bind AnyExp Tm n -> Tm n
  App :: Tm n -> Tm n -> Tm n
  TAbs :: Bind AnyExp Tm n -> Tm n
  TApp :: Tm n -> Ty n -> Tm n

-- | Aliases used for readability.
type Ty = Exp TTy

type Tm = Exp TTm

deriving instance Eq (Exp tag n)

-- | An expression that is legal at /every/ sort.
--
-- Every other constructor forces the tag to a particular sort, so 'Var' is the
-- only one that qualifies -- which is why this is just a variable. That is
-- exactly as much as can be promised when a substitution is applied to a scope
-- holding variables of mixed sorts, and it is all that the binders 'Abs' and
-- 'TAbs' need: the type-checker goes /under/ them, it never instantiates them.
newtype AnyExp n = AnyExp {anyExpVar :: Fin n}
  deriving (Eq)

-- | Use an 'AnyExp' at whichever sort is called for.
unAnyExp :: AnyExp n -> Exp tag n
unAnyExp (AnyExp x) = Var x

--------------------------------------------------------------------------------
--- Instances required by Rebound
--------------------------------------------------------------------------------

instance SubstVar AnyExp where
  var = AnyExp

instance Subst AnyExp AnyExp where
  applyE env a = applyEnv env (anyExpVar a)

-- | Renaming, at every sort at once.
--
-- Note that this cannot be written as a chain of calls to 'applyE': 'TAll'
-- binds with 'Ty' rather than 'AnyExp', so the delayed substitution held in its
-- binder has the wrong type to be composed with @env@. We force the binder and
-- rebuild it instead.
instance Subst AnyExp (Exp tag) where
  applyE :: forall n m. Env AnyExp n m -> Exp tag n -> Exp tag m
  applyE env e = case e of
    Var x -> unAnyExp (applyEnv env x)
    Kind -> Kind
    TAll bnd ->
      let (x, body) = unbindl bnd
       in TAll (bind x (applyE (up env) body))
    TArr t1 t2 -> TArr (applyE env t1) (applyE env t2)
    Abs ty bnd -> Abs (applyE env ty) (applyE env bnd)
    App t1 t2 -> App (applyE env t1) (applyE env t2)
    TAbs bnd -> TAbs (applyE env bnd)
    TApp t1 t2 -> TApp (applyE env t1) (applyE env t2)

instance SubstVar Ty where
  var = Var

-- | Substitution of types for type variables. 'Ty' is closed under its own
-- constructors, so this one is an ordinary (sort-preserving) substitution.
instance Subst Ty Ty where
  applyE :: forall n m. Env Ty n m -> Ty n -> Ty m
  applyE env t = case t of
    Var x -> applyEnv env x
    Kind -> Kind
    TAll bnd -> TAll (applyE env bnd)
    TArr t1 t2 -> TArr (applyE env t1) (applyE env t2)

-- We will be needing strengthening in the type-checker;
-- more on that later.
instance Strengthen AnyExp where
  strengthenRec k m n a = AnyExp <$> strengthenRec k m n (anyExpVar a)

instance Strengthen (Exp tag) where
  strengthenRec ::
    forall k m n.
    SNat k ->
    SNat m ->
    SNat n ->
    Exp tag (k + (m + n)) ->
    Maybe (Exp tag (k + n))
  strengthenRec k m n e = case e of
    Var x -> Var <$> strengthenRec k m n x
    Kind -> return Kind
    TAll bnd -> TAll <$> r bnd
    TArr t1 t2 -> TArr <$> r t1 <*> r t2
    Abs ty bnd -> Abs <$> r ty <*> r bnd
    App t1 t2 -> App <$> r t1 <*> r t2
    TAbs bnd -> TAbs <$> r bnd
    TApp t1 t2 -> TApp <$> r t1 <*> r t2
    where
      r :: (Strengthen c) => c (k + (m + n)) -> Maybe (c (k + n))
      r = strengthenRec k m n

--------------------------------------------------------------------------------
--- Typechecking
--------------------------------------------------------------------------------

-- | An environment mapping (de Bruijn) variables to
-- a user-defined name and its type. A type variable is recorded as having type
-- 'Kind'.
data TcEnv n = TcEnv
  { names :: Vec n LocalName,
    types :: Ctx Ty n
  }

emptyEnv :: TcEnv Z
emptyEnv = TcEnv {names = Vec.empty, types = zeroE}

-- | Add a new binding to the environment
extendE :: (LocalName, Ty n) -> TcEnv n -> TcEnv (S n)
extendE (n, t) (TcEnv ns ts) =
  TcEnv (n ::: ns) (ts +++ t)

-- | Search for a binding. Lookup cannot fail
-- thanks to extrinsic scoping.
lookupE :: TcEnv n -> Fin n -> (LocalName, Ty n)
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
push :: LocalName -> Ty n -> TC (S n) a -> TC n a
push n t = localS $ extendE (n, t)

-- | Lookup a binding in the (latent) scope.
get :: Fin n -> TC n (LocalName, Ty n)
get i = readerS (`lookupE` i)

-- | Checks that a given type is indeed a (valid) type,
-- by ensuring that its own type is 'Kind'.
ensureType :: (SNatI n) => Ty n -> TC n ()
ensureType Kind = return ()
ensureType ty = do
  k <- inferType ty
  unless (k == Kind) $ throwError "Not a type"

-- | Infer the type of an expression.
--
-- The result is a 'Ty' whatever the sort of the input: the type of a term is a
-- type, and the type of a type is 'Kind', which we also classify as a 'Ty'.
inferType :: (SNatI n) => Exp tag n -> TC n (Ty n)
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
pp :: Vec n LocalName -> Exp tag n -> String
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

    pp' :: Exp tag n -> ScopedReader PpEnv n String
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

instance Show (Exp tag Z) where
  show = pp Vec.empty

--------------------------------------------------------------------------------
--- Examples
--------------------------------------------------------------------------------

-- Note that these use the 'Var' constructor rather than 'var': 'var' comes from
-- 'SubstVar', which we only have at the 'Ty' sort (and for 'AnyExp'), whereas
-- 'Var' is polymorphic in the tag and so works in both type and term positions.

t0, t2 :: Tm Z
t1 :: Tm Z
t0 = TAbs (bind (LocalName "X") $ Abs (Var f0) (bind (LocalName "x") $ Var f0))

-- >>> t0
-- >>> runTC emptyEnv $ inferType t0
-- ΛX. λx. x
-- Right ∀X. X -> X

t1 = TAbs (bind (LocalName "X") $ Abs (TAll (bind (LocalName "Y") $ TArr (Var f0) (Var f0))) (bind (LocalName "f") $ Abs (Var f1) (bind (LocalName "x") $ App (TApp (Var f1) (Var f2)) (Var f0))))

-- >>> t1
-- >>> runTC emptyEnv $ inferType t1
-- ΛX. λf. λx. f [X] x
-- Right ∀X. (∀Y. Y -> Y) -> X -> X

t2 = Abs Kind (bind (LocalName "X") $ Abs (Var f0) (bind (LocalName "x") (Var f0)))

-- >>> t2
-- >>> runTC emptyEnv $ inferType t2
-- λX. λx. x
-- Left "Term variable occurs in type"

bbn0, bbn1, bbn2 :: Tm Z
bbn0 = TAbs (bind (LocalName "X") $ Abs (TArr (Var f0) (Var f0)) (bind (LocalName "f") $ Abs (Var f1) (bind (LocalName "z") $ Var f0)))
bbn1 = TAbs (bind (LocalName "X") $ Abs (TArr (Var f0) (Var f0)) (bind (LocalName "f") $ Abs (Var f1) (bind (LocalName "z") $ App (Var f1) (Var f0))))
bbn2 = TAbs (bind (LocalName "X") $ Abs (TArr (Var f0) (Var f0)) (bind (LocalName "f") $ Abs (Var f1) (bind (LocalName "z") $ App (Var f1) (App (Var f1) (Var f0)))))

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
