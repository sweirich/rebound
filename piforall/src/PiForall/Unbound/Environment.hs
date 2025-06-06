{- pi-forall language -}

-- | Utilities for managing a typechecking context.
module PiForall.Unbound.Environment
  ( TcMonad,
    runTcMonad,
    Env,
    emptyEnv,
    lookupTy,
    lookupTyMaybe,
    lookupDef,
    lookupHint,
    lookupTCon,
    lookupDCon,
    lookupDConAll,
    extendCtxTele,
    getCtx,
    getLocalCtx,
    extendCtx,
    extendCtxs,
    extendCtxsGlobal,
    extendCtxMods,
    extendHints,
    extendSourceLocation,
    getSourceLocation,
    err,
    warn,
    extendErr,
    D (..),
    Err (..),
    withStage,
    checkStage,
    dispErr,
  )
where

-- import PrettyPrint ( SourcePos, render, D(..), Disp(..), Doc )

import Control.Monad (unless)
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
import Control.Monad.Writer (Writer, runWriter, MonadWriter (tell))
import Data.List
import Data.Maybe (listToMaybe)
import PiForall.ConcreteSyntax qualified as C
import PiForall.Log
import PiForall.PrettyPrint
import PiForall.Unbound.NameResolution (NameResolution (..), nominalize)
import PiForall.Unbound.Syntax
import Prettyprinter (Doc, nest, pretty, sep, vcat, (<+>))
import Unbound.Generics.LocallyNameless qualified as Unbound
import qualified Data.List as List

-- | The type checking Monad includes a reader (for the
-- environment), freshness state (for supporting locally-nameless
-- representations), error (for error reporting), and IO
-- (for e.g.  warning messages).
type TcMonad = Unbound.FreshMT (ReaderT Env (ExceptT Err (Writer [Log])))

-- | Entry point for the type checking monad, given an
-- initial environment, returns either an error message
-- or some result.
runTcMonad :: Env -> TcMonad a -> (Either Err a, [Log])
runTcMonad env m =
  runWriter $
    runExceptT $
      runReaderT (Unbound.runFreshMT m) env

-- | Marked locations in the source code
data SourceLocation where
  SourceLocation :: forall a. (Display a) => SourcePos -> a -> SourceLocation

-- | Environment manipulation and accessing functions
-- The context 'gamma' is a list
data Env = Env
  { -- | elaborated term and datatype declarations
    ctx :: [ModuleEntry],
    -- | how long the tail of "global" variables in the context is
    --    (used to suppress printing those in error messages)
    globals :: Int,
    -- | Type declarations: it's not safe to
    -- put these in the context until a corresponding term
    -- has been checked.
    hints :: [TypeDecl],
    -- | what part of the file we are in (for errors/warnings)
    sourceLocation :: [SourceLocation]
  }

-- | The initial environment.
emptyEnv :: Env
emptyEnv =
  Env
    { ctx = preludeDataDecls,
      globals = length preludeDataDecls,
      hints = [],
      sourceLocation = []
    }

-- instance Disp Env where
--   disp :: Env -> Doc
--   disp e = vcat [disp decl | decl <- ctx e]
--   debugDisp :: Env -> Doc
--   debugDisp e = vcat [debugDisp decl | decl <- ctx e]

-- | Find a name's user supplied type signature.
lookupHint :: (MonadReader Env m) => TName -> m (Maybe TypeDecl)
lookupHint v = do
  hints <- asks hints
  return $ listToMaybe [sig | sig <- hints, v == declName sig]

-- | Find a name's type in the context.
lookupTyMaybe ::
  (MonadReader Env m) =>
  TName ->
  m (Maybe TypeDecl)
lookupTyMaybe v = do
  ctx <- asks ctx
  return $ go ctx
  where
    go [] = Nothing
    go (ModuleDecl sig : ctx)
      | v == declName sig = Just sig
      | otherwise = go ctx
    go (_ : ctx) = go ctx

demoteDecl :: Epsilon -> TypeDecl -> TypeDecl
demoteDecl ep s = s {declEp = min ep (declEp s)}

-- | Find the type of a name specified in the context
-- throwing an error if the name doesn't exist
lookupTy ::
  TName -> TcMonad TypeDecl
lookupTy v =
  do
    x <- lookupTyMaybe v
    gamma <- getLocalCtx
    case x of
      Just res -> return res
      Nothing ->
        err
          [ DS ("The variable " ++ show v ++ " was not found."),
            DS "in context",
            DN gamma
          ]

-- | Find a name's def in the context.
lookupDef ::
  (MonadReader Env m) =>
  TName ->
  m (Maybe Term)
lookupDef v = do
  ctx <- asks ctx
  return $ listToMaybe [a | ModuleDef v' a <- ctx, v == v']

-- | Find a type constructor in the context
lookupTCon ::
  (MonadReader Env m, MonadError Err m) =>
  TyConName ->
  m (Telescope, Maybe [ConstructorDef])
lookupTCon v = do
  g <- asks ctx
  scanGamma g
  where
    scanGamma [] = do
      currentEnv <- asks ctx
      err
        [ DS "The type constructor",
          DS v,
          DS "was not found.",
          DS "The current environment is",
          DN @[C.ModuleEntry] currentEnv
        ]
    scanGamma ((ModuleData v' delta cs) : g) =
      if v == v'
        then return (delta, Just cs)
        else scanGamma g
    scanGamma (_ : g) = scanGamma g

-- | Find a data constructor in the context, returns a list of
-- all potential matches
lookupDConAll ::
  (MonadReader Env m) =>
  DataConName ->
  m [(TyConName, (Telescope, ConstructorDef))]
lookupDConAll v = do
  g <- asks ctx
  scanGamma g
  where
    scanGamma [] = return []
    scanGamma ((ModuleData v' delta cs) : g) =
      case find (\(ConstructorDef _ v'' tele) -> v'' == v) cs of
        Nothing -> scanGamma g
        Just c -> do
          more <- scanGamma g
          return $ (v', (delta, c)) : more
    scanGamma (_ : g) = scanGamma g

-- | Given the name of a data constructor and the type that it should
-- construct, find the telescopes for its parameters and arguments.
-- Throws an error if the data constructor cannot be found for that type.
lookupDCon ::
  (MonadReader Env m, MonadError Err m) =>
  DataConName ->
  TyConName ->
  m (Telescope, Telescope)
lookupDCon c tname = do
  matches <- lookupDConAll c
  case lookup tname matches of
    Just (delta, ConstructorDef _ _ deltai) ->
      return (delta, deltai)
    Nothing ->
      err
        ( [ DS "Cannot find data constructor",
            DS c,
            DS "for type",
            DS tname,
            DS "Potential matches were:"
          ]
            ++ map (DS . fst) matches
            ++ map (DN @C.ConstructorDef . snd . snd) matches
        )

-- | Extend the context with a new entry
extendCtx :: (MonadReader Env m) => ModuleEntry -> m a -> m a
extendCtx d =
  local (\m@Env {ctx = cs} -> m {ctx = d : cs})

-- | Extend the context with a list of bindings
extendCtxs :: (MonadReader Env m) => [ModuleEntry] -> m a -> m a
extendCtxs ds =
  local (\m@Env {ctx = cs} -> m {ctx = ds ++ cs})

-- | Extend the context with a list of bindings, marking them as "global"
extendCtxsGlobal :: (MonadReader Env m) => [ModuleEntry] -> m a -> m a
extendCtxsGlobal ds =
  local
    ( \m@Env {ctx = cs} ->
        m
          { ctx = ds ++ cs,
            globals = length (ds ++ cs)
          }
    )

-- | Extend the context with a telescope
extendCtxTele :: (MonadReader Env m, MonadWriter [Log] m, MonadError Err m) => [ModuleEntry] -> m a -> m a
extendCtxTele [] m = m
extendCtxTele (ModuleDef x t2 : tele) m =
  extendCtx (ModuleDef x t2) $ extendCtxTele tele m
extendCtxTele (ModuleDecl decl : tele) m =
  extendCtx (ModuleDecl decl) $ extendCtxTele tele m
extendCtxTele (_ : tele) m =
  err [DS "Invalid telescope ", DN tele]

-- | Extend the context with a module
-- Note we must reverse the order.
extendCtxMod :: (MonadReader Env m) => Module -> m a -> m a
extendCtxMod m = extendCtxs (reverse $ moduleEntries m)

-- | Extend the context with a list of modules
extendCtxMods :: (MonadReader Env m) => [Module] -> m a -> m a
extendCtxMods mods k = foldr extendCtxMod k mods

-- | Get the complete current context
getCtx :: (MonadReader Env m) => m [ModuleEntry]
getCtx = asks ctx

-- | Get the prefix of the context that corresponds to local variables.
getLocalCtx :: (MonadReader Env m) => m [ModuleEntry]
getLocalCtx = do
  g <- asks ctx
  glen <- asks globals
  return $ take (length g - glen) g

-- | Push a new source position on the location stack.
extendSourceLocation :: (MonadReader Env m, Display t) => SourcePos -> t -> m a -> m a
extendSourceLocation p t =
  local (\e@Env {sourceLocation = locs} -> e {sourceLocation = SourceLocation p t : locs})

-- | access current source location
getSourceLocation :: (MonadReader Env m) => m [SourceLocation]
getSourceLocation = asks sourceLocation

-- | Add a type hint
extendHints :: (MonadReader Env m) => TypeDecl -> m a -> m a
extendHints h = local (\m@Env {hints = hs} -> m {hints = h : hs})

-- | An error that should be reported to the user
data Err = Err [SourceLocation] (Doc ())

data D
  = DS String
  | DD (Doc ())
  | forall a. (Display a) => DC a
  | forall a' a. (NameResolution a' a, Display a') => DN a

ddisp :: D -> (Doc ())
ddisp (DS s) = pretty s
ddisp (DD d) = d
ddisp (DC a) = disp a
ddisp (DN a) = disp $ nominalize a

-- | Augment the error message with addition information
extendErr :: (MonadError Err m) => m a -> [D] -> m a
extendErr ma d =
  ma `catchError` \(Err ps msg) -> do
    let msg' = ddisp <$> d
    throwError $ Err ps (vcat [msg, sep msg'])

instance Semigroup Err where
  (<>) :: Err -> Err -> Err
  (Err src1 d1) <> (Err src2 d2) = Err (src1 ++ src2) (d1 `mappend` d2)

instance Monoid Err where
  mempty :: Err
  mempty = Err [] mempty

dispErr :: Err -> (Doc ())
dispErr (Err [] msg) = msg
dispErr (Err ((SourceLocation p term) : _) msg) =
  display p initDI
    <+> nest 2 msg
    <+> nest 2 (pretty "In the expression" <+> nest 2 (disp term))

-- instance Disp Err where
--   disp :: Err -> Doc
--   disp = dispErr disp
--   debugDisp = dispErr debugDisp

-- | Throw an error
err :: (MonadError Err m, MonadReader Env m) => [D] -> m b
err d = do
  loc <- getSourceLocation
  throwError $ Err loc (sep $ map ddisp d)

-- | Print a warning
warn :: (MonadReader Env m, MonadWriter [Log] m) => [D] -> m ()
warn e = do
  loc <- getSourceLocation
  let msg = vcat $ ddisp <$> e
  tell $ List.singleton $ Warn $ show msg

checkStage ::
  (MonadReader Env m, MonadError Err m) =>
  Epsilon ->
  m ()
checkStage ep1 = do
  unless (ep1 <= Rel) $ do
    err
      [ DS "Cannot access",
        DS $ show ep1,
        DS "variables in this context"
      ]

withStage :: (MonadReader Env m) => Epsilon -> m a -> m a
withStage Irr = extendCtx (Demote Rel)
withStage ep = id
