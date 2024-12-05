-- | A Pretty Printer.
module PiForall.PrettyPrint (Display (..), D (..), SourcePos, PP.Doc, pp, debug) where

import Control.Monad.Reader (MonadReader (ask, local), asks)
import Data.Set qualified as S

import Text.ParserCombinators.Parsec.Error (ParseError)
import Text.ParserCombinators.Parsec.Pos (SourcePos, sourceColumn, sourceLine, sourceName)
import Prettyprinter (Doc, (<+>))
import qualified Prettyprinter as PP


import AutoEnv.Pat
import AutoEnv.Lib
import AutoEnv.Classes
import AutoEnv.Pat.LocalBind
import PiForall.Syntax

-------------------------------------------------------------------------

-- * Classes and Types for Pretty Printing

-------------------------------------------------------------------------

-- | The 'Display' class governs all types which can be turned into 'Doc's
-- The `disp` function is the main entry point for the pretty printer
-- While pretty printing, de Bruijn indices are converted into strings
-- (if possible, using the original names from the source program) using
-- information shored in the DispInfo 
class Display d where
  display :: d -> DispInfo -> Doc e

-- | Convenience entry point for the pretty printer
pp :: Display d => d -> String
pp p = show (display p initDI)

debug :: Display d => d -> String
debug p = show (display p debugDI) where
    debugDI = initDI{showLongNames = True, showAnnots=True}

-- | The data structure for information about the display
data DispInfo = DI
  { -- | should we show type annotations?
    showAnnots :: Bool,
    -- | names that have been used
    dispAvoid :: S.Set GlobalName,
    -- | current precedence level
    prec :: Int,
    -- | should we print internally-generated names, or user-friendly versions
    showLongNames :: Bool
  }

-- | Error message quoting
data D
  = -- | String literal
    DS String
  | -- | Displayable value
    forall a. Display a => DD a

initDI :: DispInfo
initDI = DI { showAnnots = False,
              dispAvoid = S.empty,
              prec = 0,
              showLongNames = False
            }


-------------------------------------------------------------------------

-- * Display Instances for quoting, errors, source positions, names

-------------------------------------------------------------------------

instance Display D where
  display (DS s) di = PP.pretty s
  display (DD d) di = PP.nest 2 $ display d di

instance Display [D] where
  display dl di = PP.sep $ map (`display` di) dl

instance Display ParseError where
  display ps di = PP.pretty (show ps)

instance Display SourcePos where
  display p di =
    PP.pretty (sourceName p) PP.<> PP.colon PP.<> PP.pretty (sourceLine p)
      PP.<> PP.colon
      PP.<> PP.pretty (sourceColumn p)
      PP.<> PP.colon


------------------------------------------------------------------------

-- * Display Instances for Modules

-------------------------------------------------------------------------

{-
instance Display Module where
  display m = do
    dn <- display (moduleName m)
    di <- mapM display (moduleImports m)
    de <- mapM display (moduleEntries m)
    pure $ PP.pretty "module" <+> dn <+> PP.pretty "where"
      $$ PP.vcat di
      $$ PP.vcat de

instance Display ModuleImport where
  display (ModuleImport i) = pure $ PP.pretty "import" <+> disp i
-}

instance Display [ModuleEntry] where
  display ds = do
    dd <- mapM display ds
    pure $ PP.vcat dd

instance Display ModuleEntry where
  display (ModuleDef n term) = do
    dn <- display n
    dt <- display term
    pure $ dn <+> PP.pretty "=" <+> dt
  display (ModuleDecl n ty) = do
    dn <- display n
    dt <- display ty
    pure $ dn <+> PP.pretty ":" <+> dt
  display (ModuleData dataDef) = display dataDef

instance Display DataDef where
    display (DataDef n params sort constructors) = do
        dn <- display n
        dp <- display params
        ds <- display sort
        dc <- mapM display constructors
        pure $ 
            ( PP.pretty "data" <+> dn <+> dp
                <+> PP.colon
                <+> ds
                <+> PP.pretty "where"
            ) <+> PP.nest 2 (PP.vcat dc)

instance Display (ConstructorDef n) where
  display (ConstructorDef c Tele) = do
    pure $ PP.pretty c
  display (ConstructorDef c tele) = do
    dc <- display c
    dt <- display tele
    pure $ dc <+> PP.pretty "of" <+> dt

-- TODO
instance Display (Telescope m n) where
   display Tele = mempty
   display (TSnoc rbnd) = undefined

-------------------------------------------------------------------------

-- * Disp Instances for Prelude types

-------------------------------------------------------------------------


displayMaybe :: (t -> DispInfo -> Doc d) -> Maybe t -> DispInfo -> Doc d
displayMaybe display m di = case m of
  (Just a) -> PP.pretty "Just" <+> display a di
  Nothing -> PP.pretty "Nothing"

instance Display a => Display (Maybe a) where
  display = displayMaybe display


displayEither :: (Display a, Display b) =>
    (forall a. Display a => a -> DispInfo -> Doc d) -> Either a b -> DispInfo -> Doc d
displayEither disp e di = case e of
     (Left a) -> PP.pretty "Left" <+> disp a di
     (Right a) -> PP.pretty "Right" <+> disp a di

instance (Display a, Display b) => Display (Either a b) where
  display = displayEither display


-------------------------------------------------------------------------

-- * Display instances for Prelude types used in AST

-------------------------------------------------------------------------

instance Display String where
  display = return . PP.pretty

instance Display Int where
  display = return . PP.pretty . show

instance Display Integer where
  display = return . PP.pretty . show

instance Display Double where
  display = return . PP.pretty . show

instance Display Float where
  display = return . PP.pretty . show

instance Display Char where
  display = return . PP.pretty . show

instance Display Bool where
  display = return . PP.pretty . show

-------------------------------------------------------------------------

-- * Display instances for Terms

-------------------------------------------------------------------------


levelApp :: Int
levelApp     = 10
levelIf :: Int
levelIf      = 0
levelLet :: Int
levelLet     = 0
levelCase :: Int
levelCase    = 0
levelLam :: Int
levelLam     = 0
levelPi :: Int
levelPi      = 0
levelSigma :: Int
levelSigma   = 0
levelProd :: Int
levelProd    = 0
levelArrow :: Int
levelArrow   = 5

withPrec :: MonadReader DispInfo m => Int -> m a -> m a
withPrec p = local (\d -> d { prec = p })

parens :: Bool -> Doc d -> Doc d
parens b = if b then PP.parens else id

brackets :: Bool -> Doc d -> Doc d
brackets b = if b then PP.brackets else id

instance Display (Term n) where
  display TyType = return $ PP.pretty "Type"
  display (Global x) = return $ PP.pretty x   -- TODO
  display (Var n) = error "TODO"  -- TODO
  display a@(Lam b) = do
    n <- ask prec
    (binds, body) <- withPrec levelLam $ gatherBinders a
    return $ parens (levelLam < n) $ (PP.pretty "\\" PP.<> PP.sep binds PP.<> PP.pretty ".") <+> PP.nest 2 body
  display (App f x) = do
    n <- ask prec
    df <- withPrec levelApp (display f)
    dx <- withPrec (levelApp+1) (display x)
    return $ parens (levelApp < n) $ df <+> dx
  display (Pi a bnd) = do
    lunbind bnd $ \(n, b) -> do
      p <- ask prec
      lhs <-
            if f0 `appearsFree` b
              then do
                dn <- display n
                da <- withPrec 0 (display a)
                return $ PP.parens (dn <+> PP.colon <+> da)
              else do
                withPrec (levelArrow+1) (display a)
      db <- withPrec levelPi (display b)
      return $ parens (levelArrow < p) $ lhs <+> PP.pretty "->" <+> db
  display (Ann a b) = do
    sa <- ask showAnnots
    if sa then do
      da <- withPrec 0 (display a)
      db <- withPrec 0 (display b)
      return $ PP.parens (da <+> PP.pretty ":" <+> db)
      else display a
  display (Pos _ e) = display e
  display (TyCon "Sigma" [tyA, Lam bnd]) =
    lunbind bnd $ \(x, tyB) -> do
      if f0 `appearsFree` tyB then do
        dx <- display x
        dA <- withPrec 0 $ display tyA
        dB <- withPrec 0 $ display tyB
        return $
          PP.pretty "{" <+> dx <+> PP.pretty ":" <+> dA
            <+> PP.pretty "|"
            <+> dB
            <+> PP.pretty "}"
        else do
          p <- ask prec
          dA <- withPrec levelSigma $ display tyA
          dB <- withPrec levelSigma $ display tyB
          return $ parens (levelSigma < p) (dA PP.<+> PP.pretty "*" PP.<+> dB)
  display (DataCon "," [a, b]) = do
    p <- ask prec
    da <- withPrec levelProd $ display a
    db <- withPrec levelProd $ display b
    return $ parens (levelProd < p) (da PP.<> PP.pretty "," PP.<> db)
  display (Let a bnd) = do
    lunbind bnd $ \(x, b) -> do
      p <- ask prec
      da <- display a
      dx <- display x
      db <- display b
      return $
        parens (levelLet < p) $
        PP.sep
          [ PP.pretty "let" <+> dx
              <+> PP.pretty "="
              <+> da
              <+> PP.pretty "in",
            db
          ]

  display t
    | Just i <- isNumeral t = display i
  display (TyCon n args) = do
    p <- ask prec
    dn <- display n
    dargs <- withPrec (levelApp+1) $ mapM display args
    return $
      parens (levelApp < p && not (null args)) (dn <+> PP.hsep dargs)
  display (DataCon n args) = do
    p <- ask prec
    dn <- display n
    dargs <- withPrec (levelApp+1) $ mapM display args
    return $
      parens (levelApp < p && not (null args)) (dn <+> PP.hsep dargs)
  display (Case scrut alts) = do
    p <- asks prec
    dscrut <- withPrec 0 $ display scrut
    dalts <- withPrec 0 $ mapM display alts
    let top = PP.pretty "case" <+> dscrut <+> PP.pretty "of"
    return $
      parens (levelCase < p) $
        if null dalts then top <+> PP.pretty "{ }" else top <+> PP.nest 2 (PP.vcat dalts)

instance Display (Match n) where
  display (Branch bd) = do
      dpat <- display (getPat bd)
      dubd <- display (getBody bd)
      return $ (dpat <+> PP.pretty "->") <+> PP.nest 2 dubd

instance Display (Pattern p n) where
  display (PatCon c PNil)   = display c
  display (PatCon c args) = do
    dc <- display c
    dargs <- display args
    return $ dc <+> dargs
      where
        wrap a@(PatVar x)      = display a
        wrap a@(PatCon _ PNil) = display a
        wrap a@(PatCon _ _)    = PP.parens <$> display a

  display (PatVar x) = display x

instance Display (PatList p n) where
  display PNil = mempty
  display (PCons p ps) = do 
    da <- display p 
    ds <- display ps
    return $ da <+> ds

-------------------------------------------------------------------------

-- * Helper functions for displaying terms

-------------------------------------------------------------------------

gatherBinders :: Term n -> DispInfo -> ([Doc d], Doc d)
gatherBinders (Lam b) =
  lunbind b $ \(n, body) -> do
    dn <- display n
    (rest, body') <- gatherBinders body
    return (dn : rest, body')
gatherBinders body = do
  db <- display body
  return ([], db)

