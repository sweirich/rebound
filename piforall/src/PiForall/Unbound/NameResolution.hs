{-# LANGUAGE FunctionalDependencies #-}

module PiForall.Unbound.NameResolution where

import Rebound (LocalName (..), internalName)
import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.State (State, StateT (..), evalStateT, gets, modify, runStateT)
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import PiForall.ConcreteSyntax qualified as C
import PiForall.Unbound.Syntax qualified as S
import Text.ParserCombinators.Parsec.Pos (initialPos)
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless qualified as Unbound

class NameResolution u r | u -> r, r -> u where
  resolve :: u -> Maybe r
  unresolve :: r -> FreshMT Identity u

resolveG :: String -> Maybe S.TName
resolveG = return . Unbound.string2Name

unresolveG :: S.TName -> FreshMT Identity String
unresolveG = return . show

instance NameResolution LocalName S.TName where
  resolve (LocalName x) = return $ Unbound.string2Name x
  unresolve = return . LocalName . takeWhile (/= '$') . Unbound.name2String

instance NameResolution C.Pattern S.Pattern where
  resolve p = evalStateT (iter p) Map.empty
    where
      -- Unbound (`unbind2` to be precise) doe not work that well with patterns
      -- which bind the same name twice, so we solve this here by "wildcarding"
      -- the first occurrences of names which appear multiple times in a
      -- pattern. Note that the wildcards themselves must be unique.
      iter :: C.Pattern -> StateT (Map.Map String Int) Maybe S.Pattern
      iter (C.PatCon n ps) = S.PatCon n . reverse <$> mapM (fmap (,S.Rel) . iter) (reverse ps)
      iter (C.PatVar (LocalName x)) = do
        i <- gets (Map.findWithDefault 0 x)
        let x' = if i == 0 then x else "_$" ++ show i
        x'' <- StateT $ \s -> (,s) <$> resolve (LocalName x')
        modify (Map.insert x (i + 1))
        return $ S.PatVar x''

  unresolve p = case p of
    S.PatCon n ps -> C.PatCon n <$> mapM (\(p, _) -> unresolve p) ps
    S.PatVar x -> C.PatVar <$> unresolve x

instance NameResolution C.Match S.Match where
  resolve (C.Branch pat t) = S.Match <$> (Unbound.bind <$> resolve pat <*> resolve t)
  unresolve (S.Match bnd) = do
    (pat, t) <- unbind bnd
    C.Branch <$> unresolve pat <*> unresolve t

instance NameResolution C.Term S.Term where
  resolve t_ = case t_ of
    C.TyType -> return S.TyType
    C.Lam x t -> S.Lam S.Rel <$> bindResolve x t
    C.Var x -> S.Var <$> resolve x
    C.Global n -> return $ S.Var $ Unbound.string2Name n
    C.Pi l x r -> S.TyPi S.Rel <$> resolve l <*> bindResolve x r
    C.Pos pos t -> S.Pos pos <$> resolve t
    C.Let x t f -> S.Let <$> resolve t <*> bindResolve x f
    C.TyCon n as -> S.TyCon n <$> mapM resolveArg as
    C.DataCon n as -> S.DataCon n <$> mapM resolveArg as
    C.Case s bs -> S.Case <$> resolve s <*> mapM resolve bs
    C.App l r -> S.App <$> resolve l <*> resolveArg r
    C.Ann t ty -> S.Ann <$> resolve t <*> resolve ty
    C.TyEq l r -> S.TyEq <$> resolve l <*> resolve r
    C.Subst l r -> S.Subst <$> resolve l <*> resolve r
    C.TmRefl -> return S.Refl
    C.Contra t -> S.Contra <$> resolve t
    C.TrustMe -> return S.TrustMe
    C.PrintMe -> return S.PrintMe
    where
      resolveArg :: C.Term -> Maybe S.Arg
      resolveArg t = S.Arg S.Rel <$> resolve t

      bindResolve :: LocalName -> C.Term -> Maybe (Unbound.Bind S.TName S.Term)
      bindResolve x t = Unbound.bind <$> resolve x <*> resolve t

  unresolve t = case t of
    S.TyType -> return C.TyType
    S.Var x -> C.Var <$> unresolve x
    S.Lam _ bnd -> do
      (x, b) <- unbind bnd
      C.Lam <$> unresolve x <*> unresolve b
    S.App l r -> C.App <$> unresolve l <*> unresolveArg r
    S.TyPi _ l bnd -> do
      (x, r) <- unbind bnd
      C.Pi <$> unresolve l <*> unresolve x <*> unresolve r
    S.Ann t ty -> C.Ann <$> unresolve t <*> unresolve ty
    S.Pos pos t -> C.Pos pos <$> unresolve t
    S.TrustMe -> return C.TrustMe
    S.PrintMe -> return C.PrintMe
    S.Let t bnd -> do
      (x, f) <- unbind bnd
      C.Let <$> unresolve x <*> unresolve t <*> unresolve f
    S.TyEq l r -> C.TyEq <$> unresolve l <*> unresolve r
    S.Refl -> return C.TmRefl
    S.Subst l r -> C.Subst <$> unresolve l <*> unresolve r
    S.Contra t -> C.Contra <$> unresolve t
    S.TyCon n args -> C.TyCon n <$> mapM unresolveArg args
    S.DataCon n args -> C.DataCon n <$> mapM unresolveArg args
    S.Case s bs -> C.Case <$> unresolve s <*> mapM unresolve bs
    where
      unresolveArg (S.Arg _ t) = unresolve t

instance NameResolution C.Telescope S.Telescope where
  resolve (C.Telescope es) = S.Telescope <$> mapM resolve es
  unresolve (S.Telescope es) = C.Telescope <$> mapM unresolve es

instance NameResolution C.ConstructorDef S.ConstructorDef where
  resolve (C.ConstructorDef pos n tele) = do
    let pos' = Maybe.fromMaybe (initialPos "prelude") pos
    S.ConstructorDef pos' n <$> resolve tele
  unresolve (S.ConstructorDef pos n tele) = C.ConstructorDef (Just pos) n <$> unresolve tele

instance NameResolution C.ModuleEntry S.ModuleEntry where
  resolve e = case e of
    C.ModuleDecl n t -> S.ModuleDecl . S.TypeDecl (Unbound.string2Name n) S.Rel <$> resolve t
    C.ModuleDef n t -> S.ModuleDef (Unbound.string2Name n) <$> resolve (t :: C.Term)
    C.ModuleData n (C.DataDef params ty cstrs) -> do
      -- TODO: what about ty?
      params' <- resolve params
      cstrs' <- mapM resolve cstrs
      return $ S.ModuleData n params' cstrs'
    C.ModuleFail _ -> error "Unsupported keyword in unbound implementation: Fail"
  unresolve e = case e of
    S.ModuleDecl (S.TypeDecl n _ t) -> C.ModuleDecl <$> unresolveG n <*> unresolve t
    S.ModuleDef n t -> C.ModuleDef <$> unresolveG n <*> unresolve t
    S.ModuleData n params cstrs -> C.ModuleData n <$> (C.DataDef <$> unresolve params <*> return C.TyType <*> mapM unresolve cstrs)
    S.Demote _ -> error "Unsupported feature in concrete syntax: Demotion"

instance NameResolution C.Entry S.Entry where
  resolve e = case e of
    C.EntryDecl n t -> S.Decl <$> (S.TypeDecl <$> resolve n <*> return S.Rel <*> resolve t)
    C.EntryDef n t -> S.Def <$> resolve n <*> resolve t
  unresolve e = case e of
    S.Decl (S.TypeDecl n _ t) -> C.EntryDecl <$> unresolve n <*> unresolve t
    S.Def n t -> C.EntryDef <$> unresolve n <*> unresolve t

instance NameResolution C.Module S.Module where
  resolve (C.Module name imports entries constructors) = do
    entries' :: [S.ModuleEntry] <- mapM resolve entries
    return $ S.Module name imports entries' constructors
  unresolve (S.Module name imports entries constructors) = do
    entries' <- mapM unresolve entries
    return $ C.Module name imports entries' constructors

instance NameResolution [C.ModuleEntry] [S.ModuleEntry] where
  resolve = mapM resolve
  unresolve = mapM unresolve

instance NameResolution [C.Entry] [S.Entry] where
  resolve = mapM resolve
  unresolve = mapM unresolve

resolveNames :: (NameResolution c s) => c -> Maybe s
resolveNames = resolve

nominalize :: (NameResolution c s) => s -> c
nominalize = runIdentity . runFreshMT . unresolve