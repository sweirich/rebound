module PiForall.Environment where

import Data.List
import Data.Maybe ( listToMaybe )
import Control.Monad.Except
    ( MonadError(..), ExceptT, runExceptT )
import Control.Monad.Reader
    ( MonadReader(local), ask, asks, ReaderT(runReaderT) )
import Text.ParserCombinators.Parsec.Pos (SourcePos)
import Prettyprinter ( Doc )

import AutoEnv hiding (Env)
import PiForall.Syntax
import PiForall.PrettyPrint


-------------------------------------------------------

-- * environment and type checking monad

-------------------------------------------------------

-- | Marked locations in the source code
data SourceLocation where
  SourceLocation :: forall a. Show a => SourcePos -> a -> SourceLocation

-- | An error that should be reported to the user
data Err = Err [SourceLocation] (Doc ())

-- | The type checking Monad includes error (for error reporting) and IO
-- (for warning messages).
-- NOTE: it would be nice if we could index the monad type with the length 
-- of the environment. However, this doesn't work well with >>= : we cannot 
-- sequence recursive calls that work in extended environments
-- So we define the Context type below that hides this length, and then 
-- dynamically check it when necessary
type TcMonad = ReaderT Env (ExceptT Err IO)

-- | Entry point for the type checking monad, given an
-- initial environment, returns either an error message
-- or some result.
runTcMonad :: TcMonad a -> IO (Either Err a)
runTcMonad m = runExceptT (runReaderT m emptyEnv)


-- | Environment manipulation and accessing functions
data Env = forall p. Env
  { 
    ctx :: Context,
    -- | local types and definitions (a telescope) 
    globals :: [ModuleEntry],
    -- | Type declarations: it's not safe to
    -- put these in the context until a corresponding term
    -- has been checked.
    hints :: [ModuleEntry],
    -- | what part of the file we are in (for errors/warnings)
    sourceLocation :: [SourceLocation]
  }

data Context = forall p. SNatI p => Context (Telescope p N0)

instance Display Context where
  display (Context t) = display t

emptyEnv :: Env
emptyEnv = Env {
  ctx = Context Tele,
  globals = prelude,
  hints = [],
  sourceLocation = []
}

lookupGlobalTy ::
  GlobalName -> TcMonad (Typ N0)
lookupGlobalTy v = do
    env <- ask
    case [a | ModuleDecl v' a <- globals env, v == v'] of
      [a] -> return a
      _  -> throwError undefined

getLocalCtx :: TcMonad Context
getLocalCtx = asks ctx

err :: [D] -> TcMonad a
err = undefined

lookupDef :: Fin n -> TcMonad (Maybe (Term n))
lookupDef = undefined