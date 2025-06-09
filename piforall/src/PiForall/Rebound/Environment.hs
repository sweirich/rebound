module PiForall.Rebound.Environment where

-- import Rebound.Scope qualified as Scope

-- import Rebound.MonadScoped qualified as SimpleScope

import Control.Monad.Except
  ( ExceptT,
    MonadError (..),
    runExceptT,
  )
import Control.Monad.IO.Class
import Control.Monad.Reader
  ( MonadReader (local),
    ReaderT (..),
    ask,
    asks,
  )
import Control.Monad.Writer (MonadWriter (..), Writer, runWriter)
import Data.Fin qualified as Fin
import Data.Foldable (Foldable (..), toList)
import Data.Kind (Type)
import Data.List
import Data.List qualified as List
import Data.Maybe (listToMaybe)
import Data.SNat qualified as Nat
import Data.Vec qualified as Vec
import PiForall.Log
import PiForall.PrettyPrint
import PiForall.Rebound.ScopeCheck qualified as ScopeCheck
import PiForall.Rebound.Syntax
import Prettyprinter (Doc, nest, pretty, sep, vcat, (<+>))
import Prettyprinter qualified as PP
import Rebound
  ( Ctx,
    Fin,
    LocalName,
    N0,
    Nat (S, Z),
    Refinement,
    SNat,
    Shiftable (..),
    Subst (applyE),
    SubstVar,
    applyEnv,
    emptyC,
    emptyR,
    weakenE',
    withSNat,
    (+++),
    type (+),
  )
import Rebound qualified
import Rebound.Bind.Local qualified as Local
import Rebound.Bind.Pat qualified as Pat
import Rebound.Bind.Scoped qualified as Scoped
import Rebound.Env (Shiftable, fromRefinement)
import Rebound.MonadNamed (Named, Sized (..))
import Rebound.MonadNamed qualified as MonadNamed
import Rebound.MonadScoped (MonadScopedReader (..))
import Rebound.MonadScoped qualified as Scoped
import Text.ParserCombinators.Parsec.Pos (SourcePos)

-------------------------------------------------------

-- * environment and type checking monad

-------------------------------------------------------

-- | Environment manipulation and accessing functions
data TcEnv (n :: Nat) = TcEnv
  { -- | Datatype definitions, top-level declarations and definitions
    globals :: [ModuleEntry],
    -- | Type declarations: it's not safe to
    -- put these in the context until a corresponding term
    -- has been checked.
    hints :: [(GlobalName, Typ Z)],
    -- | what part of the file we are in (for errors/warnings)
    sourceLocation :: [SourceLocation],
    names :: Vec.Vec n LocalName,
    types :: Ctx Term n,
    refinement :: Refinement Term n
  }

-- data NT n = NT {getName :: LocalName, getType :: Term n}

-- instance Scoped.Sized (NT n) where
--   type Size (NT n) = Nat.N1
--   size _ = Nat.s1

instance Sized (TcEnv n) where
  type Size (TcEnv n) = n
  size = Vec.vlength . names

-- instance Scope NT TcEnv where
extend :: LocalName -> Term n -> TcEnv n -> TcEnv (S n)
extend n t e =
  e
    { names = (Vec.:::) n (names e),
      types = types e +++ t,
      refinement = shift Nat.s1 (refinement e)
    }

push :: forall n p a. Telescope p n -> TcMonad (p + n) a -> TcMonad n a
push Scoped.TNil m = m
push (Scoped.TCons h t) m = case h of
  LocalDef _ _ -> push t m
  LocalDecl na ty -> push1 na ty $ push t m

push1 :: LocalName -> Term n -> TcMonad (S n) a -> TcMonad n a
push1 n t = localS (extend n t)

pushUntyped :: (Named LocalName p) => p -> TcMonad (Size p + n) a -> TcMonad n a
pushUntyped p = pushUntyped' (MonadNamed.names p)
  where
    pushUntyped' :: forall p n a. Vec.Vec p LocalName -> TcMonad (p + n) a -> TcMonad n a
    pushUntyped' Vec.VNil m = m
    pushUntyped' (h Vec.::: t) m = pushUntyped' t $ push1 h (error "No type available") m

type MonadScoped = Scoped.MonadScopedReader TcEnv

-- | The type checking Monad includes error (for error reporting) and IO
-- (for warning messages).
-- The Environment contains global declarations and definitions.
newtype TcMonad n a = TcMonad (Scoped.ScopedReaderT TcEnv (ExceptT Err (Writer [Log])) n a)
  deriving (Functor, Applicative, Monad, MonadError Err, MonadWriter [Log])

instance Scoped.MonadScopedReader TcEnv TcMonad where
  askS = TcMonad askS
  localS f (TcMonad m) = TcMonad $ localS f m

-- | Entry point for the type checking monad, given an
-- initial environment, returns either an error message
-- or some result.
runTcMonad :: TcMonad Z a -> (Either Err a, [Log])
runTcMonad (TcMonad m) =
  let e = emptyEnv
   in runWriter (runExceptT (Scoped.runScopedReaderT m e))

-- mapScope :: (t n -> t' n) -> TcMonad t' n a -> TcMonad t n a
-- mapScope f (TcMonad m) = do
--   e <- askS
--   let e' = e {types = f $ types e}
--   let (r, logs) = runWriter (runExceptT (Scoped.runScopedReaderT m e'))
--   tell logs
--   case r of
--     Left err -> throwError err
--     Right v -> return v

-- | Initial environment
emptyEnv :: TcEnv Z
emptyEnv =
  TcEnv
    { globals = prelude,
      hints = [],
      sourceLocation = [],
      names = Vec.empty,
      types = Rebound.zeroE,
      refinement = emptyR
    }

scopeSize :: TcMonad n (Nat.SNat n)
scopeSize = readerS (size :: TcEnv n -> Nat.SNat n)

withScopeSize :: ((Nat.SNatI n) => TcMonad n u) -> TcMonad n u
withScopeSize k = do
  s <- scopeSize
  withSNat s k

getRefinement :: TcMonad n (Refinement Term n)
getRefinement = readerS refinement

refine :: Term n -> TcMonad n (Term n)
refine t = do
  r <- getRefinement
  withScopeSize $ return $ Rebound.refine r t

--------------------------------------------------------------------
-- Globals

-- | Find a name's user supplied type signature
lookupHint :: (MonadScoped m) => GlobalName -> m n (Maybe (Typ n))
lookupHint v = do
  hints <- readerS hints
  return $ listToMaybe [weakenClosed ty | (x, ty) <- hints, v == x]

lookupGlobalTy :: GlobalName -> TcMonad n (Typ n)
lookupGlobalTy v = do
  env <- askS
  case [a | ModuleDecl v' a <- globals env, v == v'] of
    [a] -> return (weakenClosed a)
    _ -> do
      mty <- lookupHint v
      case mty of
        Just ty -> return ty
        Nothing -> err [DS $ "The variable " ++ show v ++ " was not found"]

lookupGlobalDef :: GlobalName -> TcMonad n (Term n)
lookupGlobalDef v = do
  env <- askS
  case [a | ModuleDef v' a <- globals env, v == v'] of
    [a] -> return (weakenClosed a)
    _ ->
      err
        [ DS ("The variable " ++ show v ++ " was not found"),
          DS "(out of scope)"
        ]

-- | Find the datatype declaration of a type constructor in the context
lookupTCon :: TyConName -> TcMonad n DataDef
lookupTCon v = do
  g <- readerS globals
  scanGamma g
  where
    scanGamma [] = do
      currentEnv <- readerS globals
      err $
        [ DS "The type constructor",
          DC v,
          DS "was not found.",
          DS "The current environment is"
        ]
          <> (DZ <$> currentEnv)
    scanGamma ((ModuleData n d) : g) =
      if n == v
        then return d
        else scanGamma g
    scanGamma (_ : g) = scanGamma g

-- | Find a data constructor in the context, returns a list of
-- all potential matches
lookupDConAll ::
  DataConName ->
  TcMonad n [(TyConName, ScopedConstructorDef)]
lookupDConAll v = do
  g <- readerS globals
  scanGamma g
  where
    scanGamma [] = return []
    scanGamma ((ModuleData tn (DataDef delta _ cs)) : g) =
      case find (\(ConstructorDef v'' _) -> v'' == v) cs of
        Nothing -> scanGamma g
        Just c -> do
          more <- scanGamma g
          return $
            ( tn,
              ScopedConstructorDef delta c
            )
              : more
    scanGamma (_ : g) = scanGamma g

-- | Given the name of a data constructor and the type that it should
-- construct, find the telescopes for its parameters and arguments.
-- Throws an error if the data constructor cannot be found for that type.
lookupDCon ::
  DataConName ->
  TyConName ->
  TcMonad n ScopedConstructorDef
lookupDCon c tname = do
  matches <- lookupDConAll c
  case lookup tname matches of
    Just scd -> return scd
    Nothing ->
      err
        ( [ DS "Cannot find data constructor",
            DS c,
            DS "for type",
            DC tname,
            DS "Potential matches were:"
          ]
            ++ map (DC . fst) matches
        )

--------------------------------------------------------------------

-- | A local context is an environment that binds n variables (and may also
-- include local definitions).
type Context a = Ctx Term a

weakenDef :: SNat n -> (Fin p, Term p) -> (Fin (n + p), Term (n + p))
weakenDef m (x, y) = (Fin.weakenFin m x, applyE @Term (weakenE' m) y)

emptyContext :: Context N0
emptyContext = emptyC

-- | Find the type of a local variable in the context
-- This cannot fail
lookupTy :: (MonadScoped m) => Fin n -> m n (Term n)
lookupTy x = readerS (\e -> applyEnv (types e) x)

-- | Extend the context with a new declaration
extendTy :: Typ n -> Context n -> Context (S n)
extendTy d gamma = gamma +++ d

--------------------------------------------------------------------
-- Source locations

-- | Marked locations in the source code
data SourceLocation where
  SourceLocation :: forall n u s t. (ScopeCheck.Scoping n u s, Display u) => SourcePos -> s -> TcEnv n -> SourceLocation

-- | Push a new source position on the location stack.
extendSourceLocation :: (ScopeCheck.Scoping n u s, Display u) => SourcePos -> s -> TcMonad n a -> TcMonad n a
extendSourceLocation p t m = do
  s <- askS
  Scoped.localS
    ( \e@TcEnv {sourceLocation = locs} ->
        e {sourceLocation = SourceLocation p t s : locs}
    )
    m

-- | access current source location
getSourceLocation :: (MonadScoped m) => m n [SourceLocation]
getSourceLocation = readerS sourceLocation

--------------------------------------------------------------------
-- Errors

-- | An error that should be reported to the user
data Err = Err [SourceLocation] (Doc ())

instance Semigroup Err where
  (<>) :: Err -> Err -> Err
  (Err src1 d1) <> (Err src2 d2) = Err (src1 ++ src2) (d1 `mappend` d2)

instance Monoid Err where
  mempty :: Err
  mempty = Err [] mempty

-- | Scoped error message quoting
data D n
  = DS String
  | DD (Doc ())
  | -- An unscoped value
    forall a. (Display a) => DC a
  | -- A value in the current scope
    forall u s. (ScopeCheck.Scoping n u s, Display u) => DU s
  | -- A value in the empty scope
    forall u s. (ScopeCheck.Scoping Z u s, Display u) => DZ s
  | DR (Refinement Term n)

scopedDisplay :: (ScopeCheck.Scoping n u s, Display u) => s -> TcEnv n -> Doc ()
scopedDisplay t e@TcEnv {names = sc} =
  let -- sc = Scope.projectScope s
      t' = withSNat (Vec.vlength sc) ScopeCheck.unscopeUnder sc t
   in disp t'

sdisplay :: D n -> DispInfo -> TcMonad n (Doc ())
sdisplay (DS s) di = return $ PP.pretty s
sdisplay (DD d) di = return d
sdisplay (DC c) di = return $ disp c
sdisplay (DU s) di = scopedDisplay s <$> askS
sdisplay (DZ s) di = return $ scopedDisplay s emptyEnv
sdisplay (DR r) di = do
  ss <- scopeSize
  s <- readerS names
  let r' = withSNat ss $ fromRefinement r
  let t' = toList $ withSNat ss $ ScopeCheck.unscopeUnder s (ss, r')
  let c :: [Doc ()] = (\(i, t) -> disp i <+> PP.pretty "|-->" <+> disp t) <$> zip (toList s) t'
  return $ PP.vcat c

displayContext :: TcMonad n (D n)
displayContext = do
  ss <- scopeSize
  (names, types) <- readerS (\e -> (names e, types e))
  let t' = toList $ ScopeCheck.unscopeUnder Vec.empty (ss, names, types)
  let c :: [Doc ()] = (\(i, t) -> disp i <+> PP.pretty ":" <+> disp t) <$> t'
  return $ DD $ PP.vcat c

displayRefinement :: TcMonad n (D n)
displayRefinement = DR <$> readerS refinement

-- | display an error
-- TODO: preserve passed in di for printing the term???
displayErr :: Err -> DispInfo -> Doc ()
displayErr (Err [] msg) di = msg
displayErr (Err ((SourceLocation p term s) : _) msg) di =
  display p di
    <+> nest 2 msg
    <+> nest
      2
      ( pretty "\nin the expression"
          <+> nest 2 (scopedDisplay term s)
      )

-- | Print a warning
warn :: [D n] -> TcMonad n ()
warn d = do
  loc <- getSourceLocation
  msg <- mapM (`sdisplay` initDI) d
  tell $ List.singleton $ Warn $ show $ vcat msg

-- | Print an error, making sure that the scope lines up
err :: [D n] -> TcMonad n b
err d = do
  loc <- getSourceLocation
  msg <- mapM (`sdisplay` initDI) d
  throwError $ Err loc (sep msg)

-- | Augment an error message with addition information (if thrown)
extendErr :: TcMonad n a -> [D n] -> TcMonad n a
extendErr ma d =
  ma `catchError` \(Err ps msg) -> do
    msg' <- mapM (`sdisplay` initDI) d
    throwError $ Err ps (vcat [msg, sep msg'])

whenNothing :: Maybe a -> [D n] -> TcMonad n a
whenNothing x msg =
  case x of
    Just r -> return r
    Nothing -> err msg

ensureError :: TcMonad n a -> TcMonad n (Either Err a)
ensureError c = (Right <$> c) `catchError` \err -> return $ Left err

--------------------------------------------------------------
-- Modules

-- | Add a type hint
extendHints :: (MonadScoped m) => (GlobalName, Typ Z) -> m n a -> m n a
extendHints h = localS (\m@TcEnv {hints = hs} -> m {hints = h : hs})

-- | Extend the global environment with a new entry
extendCtx :: (MonadScoped m) => ModuleEntry -> m n a -> m n a
extendCtx d =
  localS (\m@TcEnv {globals = cs} -> m {globals = d : cs})

-- | Extend the context with a list of global bindings
extendCtxs :: (MonadScoped m) => [ModuleEntry] -> m n a -> m n a
extendCtxs ds =
  localS (\m@TcEnv {globals = cs} -> m {globals = ds ++ cs})

-- | Extend the context with a module
-- Note we must reverse the order
extendCtxMod :: (MonadScoped m) => Module -> m n a -> m n a
extendCtxMod m = extendCtxs (reverse $ moduleEntries m)

-- | Extend the context with a list of modules
extendCtxMods :: (MonadScoped m) => [Module] -> m n a -> m n a
extendCtxMods mods k = foldr extendCtxMod k mods