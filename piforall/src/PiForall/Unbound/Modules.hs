{- pi-forall language -}

-- | Tools for working with multiple source files
module PiForall.Unbound.Modules (goFilename, getModules, ModuleInfo (..)) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Lazy
import Data.Graph qualified as Gr
import Data.List (nub, (\\))
import PiForall.ConcreteSyntax qualified as C
import PiForall.Parser
import PiForall.PrettyPrint
import PiForall.Unbound.Environment
import PiForall.Unbound.NameResolution qualified as NameResolution
import PiForall.Unbound.Syntax
import PiForall.Unbound.TypeCheck
import System.Directory
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import System.FilePath
import Text.ParserCombinators.Parsec.Error (ParseError, errorPos)

-- | getModules starts with a top-level module, and gathers all of the module's
-- transitive dependency. It returns the list of parsed modules, with all
-- modules appearing after its dependencies.
getModules ::
  (Functor m, MonadError ParseError m, MonadIO m) =>
  [FilePath] ->
  String ->
  m [Module]
getModules prefixes top = do
  toParse <- gatherModules prefixes [ModuleImport top]
  flip evalStateT initialConstructorNames $ mapM reparse toParse

data ModuleInfo = ModuleInfo
  { modInfoName :: ModuleName,
    modInfoFilename :: String,
    modInfoImports :: [ModuleImport]
  }

-- | Build the module dependency graph.
--   This only parses the imports part of each file; later we go back and parse all of it.
gatherModules ::
  (Functor m, MonadError ParseError m, MonadIO m) =>
  [FilePath] ->
  [ModuleImport] ->
  m [ModuleInfo]
gatherModules prefixes ms = gatherModules' ms []
  where
    gatherModules' [] accum = return $ topSort accum
    gatherModules' ((ModuleImport m) : ms') accum = do
      modFileName <- getModuleFileName prefixes m
      imports <- C.moduleImports <$> parseModuleImports modFileName
      let accum' = ModuleInfo m modFileName imports : accum
      let oldMods = map (ModuleImport . modInfoName) accum'
      gatherModules' (nub (ms' ++ imports) \\ oldMods) accum'

-- | Generate a sorted list of modules, with the postcondition that a module
-- will appear _after_ any of its dependencies.
topSort :: [ModuleInfo] -> [ModuleInfo]
topSort ms = reverse sorted
  where
    (gr, lu) =
      Gr.graphFromEdges'
        [ (m, modInfoName m, [i | ModuleImport i <- modInfoImports m])
          | m <- ms
        ]
    lu' v = let (m, _, _) = lu v in m
    sorted = [lu' v | v <- Gr.topSort gr]

-- | Find the file associated with a module.
getModuleFileName ::
  (MonadIO m) =>
  [FilePath] ->
  ModuleName ->
  m FilePath
getModuleFileName prefixes modul = do
  let makeFileName prefix = prefix </> mDotPi
      -- get M.pi from M or M.pi
      mDotPi =
        if takeExtension s == ".pi"
          then s
          else s <.> "pi"
      s = modul
      possibleFiles = map makeFileName prefixes
  files <- liftIO $ filterM doesFileExist possibleFiles
  if null files
    then
      error $
        "Can't locate module: "
          ++ show modul
          ++ "\nTried: "
          ++ show possibleFiles
    else return $ head files

-- | Fully parse a module (not just the imports).
reparse ::
  (MonadError ParseError m, MonadIO m, MonadState ConstructorNames m) =>
  ModuleInfo ->
  m Module
reparse (ModuleInfo _ fileName _) = do
  cnames <- get
  modu <- parseModuleFile cnames fileName
  put (C.moduleConstructors modu)
  case NameResolution.resolve modu of
    Just m -> return m
    Nothing -> error "name resolution failed"

exitWith :: Either a b -> (a -> IO ()) -> IO b
exitWith res f =
  case res of
    Left x -> f x >> exitFailure
    Right y -> return y

-- | Type check the given string in the empty environment
go :: String -> IO ()
go str = do
  case parseExpr str of
    Left parseError -> putParseError parseError
    Right term ->
      case NameResolution.resolve term of
        Nothing -> error "name resolution failed"
        Just m -> do
          putStrLn "parsed as"
          exitSuccess
          putStrLn $ pp $ NameResolution.nominalize m
          let (res, logs) = runTcMonad emptyEnv (inferType m)
          mapM_ print logs
          case res of
            Left typeError -> putTypeError (dispErr typeError)
            Right ty -> do
              putStrLn "typed with type"
              putStrLn $ pp $ NameResolution.nominalize ty

-- | Display a parse error to the user
putParseError :: ParseError -> IO ()
putParseError parseError = do
  putStrLn $ pp $ errorPos parseError
  print parseError

-- | Display a type error to the user
putTypeError :: Doc () -> IO ()
putTypeError typeError = do
  putStrLn "Type Error:"
  print typeError

-- | Type check the given file
goFilename :: [String] -> String -> IO ()
goFilename extras pathToMainFile = do
  let prefixes = [currentDir, mainFilePrefix] ++ extras
      (mainFilePrefix, name) = splitFileName pathToMainFile
      currentDir = ""
  putStrLn $ "processing " ++ name ++ "..."
  v <- runExceptT (getModules prefixes name)
  val <- v `exitWith` putParseError
  putStrLn "type checking..."
  let (d, logs) = runTcMonad emptyEnv (tcModules val)
  mapM_ print logs
  defs <- d `exitWith` (putTypeError . dispErr)
  putStrLn $ pp $ NameResolution.nominalize (last defs)

-- | 'pi <filename>' invokes the type checker on the given
-- file and either prints the types of all definitions in the module
-- or prints an error message.
main :: IO ()
main = do
  [pathToMainFile] <- getArgs
  goFilename [] pathToMainFile
  exitSuccess