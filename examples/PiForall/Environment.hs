module PiForall.Environment where

import Data.List
import Data.Maybe ( listToMaybe )
import Control.Monad.Except
    ( MonadError(..), ExceptT, runExceptT )
import Control.Monad.Reader
    ( MonadReader(local), ask, asks, ReaderT(runReaderT) )
import Text.ParserCombinators.Parsec.Pos (SourcePos)
import Prettyprinter ( Doc, vcat, sep, (<+>), nest, pretty )

import AutoEnv.Context

import AutoEnv
import AutoEnv.Pat.Rebind
import PiForall.Syntax
import PiForall.PrettyPrint


-------------------------------------------------------

-- * environment and type checking monad

-------------------------------------------------------


-- | The type checking Monad includes error (for error reporting) and IO
-- (for warning messages).
-- The Environment contains global declarations and definitions.
type TcMonad = ReaderT TcEnv (ExceptT Err IO)

-- | Entry point for the type checking monad, given an
-- initial environment, returns either an error message
-- or some result.
runTcMonad :: TcMonad a -> IO (Either Err a)
runTcMonad m = runExceptT (runReaderT m emptyEnv)

-- | Environment manipulation and accessing functions
data TcEnv = TcEnv
  {
    -- | Datatype definitions, top-level declarations and definitions
    globals :: [ModuleEntry],
    -- | Type declarations: it's not safe to
    -- put these in the context until a corresponding term
    -- has been checked.
    hints :: [ModuleEntry],
    -- | what part of the file we are in (for errors/warnings)
    sourceLocation :: [SourceLocation]
  }


-- | Initial environment
emptyEnv :: TcEnv
emptyEnv = TcEnv {
  globals = prelude,
  hints = [],
  sourceLocation = []
}


--------------------------------------------------------------------
-- Globals


-- | Find a name's user supplied type signature
lookupHint :: (MonadReader TcEnv m) => GlobalName -> m (Maybe ModuleEntry)
lookupHint v = do
  hints <- asks hints
  return $ listToMaybe [ sig | sig <- hints, v == declName sig]

lookupGlobalTy ::
  GlobalName -> TcMonad (Typ n)
lookupGlobalTy v = do
    env <- ask
    case [a | ModuleDecl v' a <- globals env, v == v'] of
      [a] -> return a
      _  -> err [ DS ("The variable " ++ show v ++ " was not found."),
            DS "in the global context."
                      ]
lookupGlobalDef ::
  GlobalName -> TcMonad (Term n)
lookupGlobalDef v = do
    env <- ask
    case [a | ModuleDef v' a <- globals env, v == v'] of
      [a] -> return a
      _  -> err [ DS ("The variable " ++ show v ++ " was not found."),
            DS "in the global context."]

-- | Find a type constructor in the context
lookupTCon ::
  (MonadReader TcEnv m, MonadError Err m) =>
  TyConName -> m DataDef
lookupTCon v = do
  g <- asks globals
  scanGamma g
  where
    scanGamma [] = do
      currentEnv <- asks globals
      err
        [ DS "The type constructor",
          DD v,
          DS "was not found.",
          DS "The current environment is",
          DD currentEnv
        ]
    scanGamma ((ModuleData n d) : g) =
      if n == v
        then return d
        else scanGamma g
    scanGamma (_ : g) = scanGamma g

-- | Find a data constructor in the context, returns a list of
-- all potential matches
lookupDConAll ::
  (MonadReader TcEnv m) =>
  DataConName ->
  m [(TyConName, ScopedConstructorDef)]
lookupDConAll v = do
  g <- asks globals
  scanGamma g
  where
    scanGamma [] = return []
    scanGamma ((ModuleData _ (DataDef delta _ cs)) : g) =
      case find (\(ConstructorDef v'' tele) -> v'' == v) cs of
        Nothing -> scanGamma g
        Just c -> do
          more <- scanGamma g
          return $ (v, 
             ScopedConstructorDef delta c) :  more
    scanGamma (_ : g) = scanGamma g

-- | Given the name of a data constructor and the type that it should
-- construct, find the telescopes for its parameters and arguments.
-- Throws an error if the data constructor cannot be found for that type.
lookupDCon ::
  (MonadReader TcEnv m, MonadError Err m) =>
  DataConName ->
  TyConName ->
  m ScopedConstructorDef
lookupDCon c tname = do
  matches <- lookupDConAll c
  case lookup tname matches of
    Just scd -> return scd
    Nothing ->
      err
        ( [ DS "Cannot find data constructor",
            DS c,
            DS "for type",
            DD tname,
            DS "Potential matches were:"
          ]
            ++ map (DD . fst) matches
        )


--------------------------------------------------------------------

-- | A local context is an environment that binds n variables (and may also 
-- include local definitions). 
data Context n = Context {
    local_size  :: SNat n,
    local_decls :: Ctx Term n
    -- local_defs  :: Env Term m n 
}

weakenDef :: SNat n -> (Fin p, Term p) -> (Fin (Plus n p), Term (Plus n p))
weakenDef m (x,y) = (weakenFin m x, applyE @Term (weakenE' m) y)

emptyContext :: Context N0
emptyContext = Context s0 emptyC -- emptyE

instance Display (Context n) where
  display (Context { local_decls = decls}) di = pretty "TODO <display context>"

{-
getLocalCtx :: forall n. SNatI n => TcMonad (Ctx Term n)
getLocalCtx = do 
  c <- asks ctx
  case c of 
    Context _ (t :: Ctx Term p) _ ->
         case testEquality @_ @n snat (snat :: SNat p) of 
           Just Refl -> return t
           Nothing -> err [DS "invalid scope"]

getLocalDefs :: forall n. SNatI n => TcMonad [(Fin n, Term n)]
getLocalDefs = do 
  c <- asks ctx
  case c of 
    Context _ _ (t :: [(Fin p, Term p)]) ->
         case testEquality @_ @n snat (snat :: SNat p) of 
           Just Refl -> return t
           Nothing -> err [DS "invalid scope"]
-}

{-
lookupDef :: Fin m -> Context m n -> TcMonad (Maybe (Term n))
lookupDef x (Context _ _ gamma) = go gamma 
    where
      go [] = return Nothing
      go ((y,u):t) = if x == y then return (Just u) else go t
-}        

{-
-- | Extend with new definitions
extendDecls :: [(Fin n, Term n)] -> Context m n -> Context m n 
extendDecls d c@(Context gamma defs) = Context n gamma (d ++ defs)
-}

-- | Find the type of a local variable in the context
-- This cannot fail
lookupTy :: Fin n -> Context n -> Term n
lookupTy x (Context {local_decls = gamma}) = applyEnv gamma x

-- | Extend the context with a new declaration
extendTy :: Term n -> Context n -> Context (S n) 
extendTy d c@(Context {local_size=n,local_decls=gamma}) = c { local_size = SS n,local_decls =gamma +++ d }
  -- (map (weakenDef s1) defs)

extendLocal :: Local p n -> (Context (Plus p n) -> m a) -> (Context n -> m a)
extendLocal (LocalDecl x t) k ctx = k (extendTy t ctx)
extendLocal (LocalDef x u) k ctx = error "TODO: local definitions unsupported"

--------------------------------------------------------------------
-- Source locations 

-- | Marked locations in the source code
data SourceLocation where
  SourceLocation :: forall a. Display a => SourcePos -> a -> SourceLocation

-- | Push a new source position on the location stack.
extendSourceLocation :: (MonadReader TcEnv m, Display t) => SourcePos -> t -> m a -> m a
extendSourceLocation p t =
  local (\e@TcEnv {sourceLocation = locs} -> e {sourceLocation = SourceLocation p t : locs})

-- | access current source location
getSourceLocation :: MonadReader TcEnv m => m [SourceLocation]
getSourceLocation = asks sourceLocation

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

-- | display an error
displayErr :: Err -> DispInfo -> Doc ()
displayErr (Err [] msg) di = msg
displayErr (Err ((SourceLocation p term) : _) msg) di =
    display p di
      <+> nest 2 msg
      <+> nest 2 (pretty "In the expression" 
                 <> nest 2 (display term di))

-- | Throw an error
err :: (Display a, MonadError Err m, MonadReader TcEnv m) => [a] -> m b
err d = do
  loc <- getSourceLocation
  throwError $ Err loc (sep $ map (`display` initDI) d)

-- | Augment an error message with addition information (if thrown)
extendErr :: MonadError Err m => m a -> Doc () -> m a
extendErr ma msg' =
  ma `catchError` \(Err ps msg) ->
    throwError $ Err ps (vcat [msg, msg'])


