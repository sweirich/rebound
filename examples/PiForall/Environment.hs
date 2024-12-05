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
type TcMonad n = ReaderT (Env n) (ExceptT Err IO)

-- | Entry point for the type checking monad, given an
-- initial environment, returns either an error message
-- or some result.
runTcMonad :: TcMonad N0 a -> IO (Either Err a)
runTcMonad m = runExceptT (runReaderT m emptyEnv)


-- | Environment manipulation and accessing functions
-- The context 'gamma' is a list
data Env p = Env
  { -- | Local variables 
    ctx :: Telescope p N0,
    -- | 
    globals :: [ModuleEntry],
    -- | Type declarations: it's not safe to
    -- put these in the context until a corresponding term
    -- has been checked.
    hints :: [ModuleEntry],
    -- | what part of the file we are in (for errors/warnings)
    sourceLocation :: [SourceLocation]
  }

emptyEnv :: Env N0
emptyEnv = Env {
  ctx = Tele,
  globals = prelude,
  hints = [],
  sourceLocation = []
}

lookupGlobalTy ::
  GlobalName -> TcMonad n (Typ N0)
lookupGlobalTy v = do
    env <- ask
    case [a | ModuleDecl v' a <- globals env, v == v'] of
      [a] -> return a
      _  -> throwError undefined

getLocalCtx :: TcMonad n (Telescope n N0)
getLocalCtx = asks ctx
