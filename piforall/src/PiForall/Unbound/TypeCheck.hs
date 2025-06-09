{- pi-forall -}

-- | The main routines for type-checking
module PiForall.Unbound.TypeCheck (tcModules, inferType, checkType) where

import Control.Monad (foldM, unless, zipWithM, zipWithM_)
import Control.Monad.Except
import Control.Monad.IO.Class
import Data.List (nub)
import Data.Maybe (catMaybes)
import PiForall.Unbound.Environment (D (..), TcMonad)
import PiForall.Unbound.Environment qualified as Env
import PiForall.Unbound.Equal qualified as Equal
import PiForall.Unbound.NameResolution qualified as NameResolution
import PiForall.Unbound.Syntax
import Prettyprinter (Doc, nest, pretty, sep, vcat, (<+>))
import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import qualified Data.List as List
import PiForall.Log
import Control.Monad.Writer (MonadWriter(..))

---------------------------------------------------------------------

-- | Infer/synthesize the type of a term
inferType :: Term -> TcMonad Type
inferType a = case a of
  -- i-var
  (Var x) -> do
    decl <- Env.lookupTy x -- make sure the variable is accessible
    Env.checkStage (declEp decl)
    return (declType decl)

  -- i-type
  TyType -> return TyType
  -- i-pi
  (TyPi ep tyA bnd) -> do
    (x, tyB) <- unbind bnd
    tcType tyA
    Env.extendCtx (ModuleDecl (TypeDecl x ep tyA)) (tcType tyB)
    return TyType

  -- i-app
  (App a b) -> do
    ty1 <- inferType a
    ty1' <- Equal.whnf ty1
    case ty1' of
      (TyPi {- SOLN EP -} ep1 {- STUBWITH -} tyA bnd) -> do
        unless (ep1 == argEp b) $
          Env.err
            [ DS "In application, expected",
              DS $ show ep1,
              DS "argument but found",
              DN $ unArg b,
              DS "instead."
            ]
        -- if the argument is Irrelevant, resurrect the context
        (if ep1 == Irr then Env.extendCtx (Demote Rel) else id) $ checkType (unArg b) tyA
        return (instantiate bnd (unArg b))
      _ -> Env.err [DS "Expected a function type but found ", DN ty1]

  -- i-ann
  (Ann a tyA) -> do
    tcType tyA
    checkType a tyA
    return tyA

  -- Practicalities
  -- remember the current position in the type checking monad
  (Pos p a) ->
    Env.extendSourceLocation p (NameResolution.nominalize a) $ inferType a
  -- i-eq
  (TyEq a b) -> do
    aTy <- inferType a
    checkType b aTy
    return TyType

  -- Type constructor application
  (TyCon c params) -> do
    (Telescope delta, _) <- Env.lookupTCon c
    unless (length params == length delta) $
      Env.err
        [ DS "Datatype constructor",
          DS c,
          DS $
            "should have "
              ++ show (length delta)
              ++ "parameters, but was given",
          DS $ show (length params)
        ]
    tcArgTele params delta
    return TyType

  -- Data constructor application
  -- we don't know the expected type, so see if there
  -- is only one datacon of that name that takes no
  -- parameters
  (DataCon c args) -> do
    matches <- Env.lookupDConAll c
    case matches of
      [(tname, (Telescope [], ConstructorDef _ _ (Telescope deltai)))] -> do
        let numArgs = length deltai
        unless (length args == numArgs) $
          Env.err
            [ DS "Constructor",
              DS c,
              DS "should have",
              DS $ show numArgs,
              DS "data arguments, but was given",
              DS $ show (length args),
              DS "arguments."
            ]
        tcArgTele args deltai
        return $ TyCon tname []
      [_] ->
        Env.err
          [ DS "Cannot infer the parameters to data constructors.",
            DS "Add an annotation."
          ]
      _ -> Env.err [DS "Ambiguous data constructor", DS c]

  -- cannot synthesize the type of the term
  _ ->
    Env.err [DS "Must have a type annotation for", DN a]

-------------------------------------------------------------------------

-- | Make sure that the term is a "type" (i.e. that it has type 'Type')
tcType :: Term -> TcMonad ()
tcType tm = Env.withStage Irr $ checkType tm TyType

-------------------------------------------------------------------------

-- | Check that the given term has the expected type
checkType :: Term -> Type -> TcMonad ()
checkType tm ty = do
  ty' <- Equal.whnf ty
  case tm of
    -- c-lam: check the type of a function
    (Lam ep1 bnd) -> case ty' of
      (TyPi ep2 tyA bnd2) -> do
        -- unbind the variables in the lambda expression and pi type
        (x, body, tyB) <- unbind2 bnd bnd2
        -- epsilons should match up
        unless (ep1 == ep2) $
          Env.err
            [ DS "In function definition, expected",
              DS $ show ep2,
              DS "parameter",
              DN x,
              DS "but found",
              DS $ show ep1,
              DS "instead."
            ]
        -- check the type of the body of the lambda expression
        Env.extendCtx (ModuleDecl (TypeDecl x ep1 tyA)) (checkType body tyB)
      _ -> Env.err [DS "Lambda expression should have a function type, not", DN ty']
    -- Practicalities
    (Pos p a) ->
      Env.extendSourceLocation p (NameResolution.nominalize a) $ checkType a ty'
    TrustMe -> return ()
    PrintMe -> do
      gamma <- Env.getLocalCtx
      Env.warn
        [ DS "Unmet obligation.\nContext:",
          DN gamma,
          DS "\nGoal:",
          DN ty'
        ]
    -- c-let
    (Let a bnd) -> do
      (x, b) <- unbind bnd
      tyA <- inferType a
      Env.extendCtxs [promote $ mkDecl x tyA, ModuleDef x a] $
        checkType b ty'
    -- c-refl
    Refl -> case ty' of
      (TyEq a b) -> Equal.equate a b
      _ -> Env.err [DS "Refl annotated with invalid type", DN ty']
    -- c-subst
    (Subst a b) -> do
      -- infer the type of the proof 'b'
      tp <- inferType b
      -- make sure that it is an equality between m and n
      nf <- Equal.whnf tp
      (m, n) <- case nf of
        TyEq m n -> return (m, n)
        _ -> Env.err [DS "Subst requires an equality type, not", DN tp]
      -- if either side is a variable, add a definition to the context
      edecl <- Equal.unify [] m n
      -- if proof is a variable, add a definition to the context
      pdecl <- Equal.unify [] b Refl
      Env.extendCtxs (promote <$> (edecl ++ pdecl)) $ checkType a ty'
    -- c-contra
    (Contra p) -> do
      ty' <- inferType p
      nf <- Equal.whnf ty'
      (a, b) <- case nf of
        TyEq m n -> return (m, n)
        _ -> Env.err [DS "Contra requires an equality type, not", DN ty']
      a' <- Equal.whnf a
      b' <- Equal.whnf b
      case (a', b') of
        (DataCon da _, DataCon db _)
          | da /= db ->
              return ()
        (_, _) ->
          Env.err
            [ DS "I can't tell that",
              DN a,
              DS "and",
              DN b,
              DS "are contradictory"
            ]

    -- c-data
    -- we know the expected type of the data constructor
    -- so look up its type in the context
    (DataCon c args) -> do
      case ty' of
        (TyCon tname params) -> do
          (Telescope delta, Telescope deltai) <- Env.lookupDCon c tname
          let isDecl :: Entry -> Bool
              isDecl (Decl _) = True
              isDecl _ = False
          let numArgs = length (filter isDecl deltai)
          unless (length args == numArgs) $
            Env.err
              [ DS "Constructor",
                DS c,
                DS "should have",
                DS $ show numArgs,
                DS "data arguments, but was given",
                DS $ show (length args),
                DS "arguments."
              ]
          newTele <- substTele delta params deltai
          tcArgTele args newTele
        _ ->
          Env.err [DS "Unexpected type", DN ty', DS "for data constructor", DN tm]
    (Case scrut alts) -> do
      sty <- inferType scrut
      (c, args) <- Equal.ensureTCon sty
      scrut' <- Equal.whnf scrut
      let checkAlt (Match bnd) = do
            (pat, body) <- Unbound.unbind bnd
            -- add variables from pattern to context
            -- could fail if branch is in-accessible
            decls <- declarePat pat Rel (TyCon c args)
            -- add defs to the contents from scrut = pat
            -- could fail if branch is in-accessible
            decls' <- Equal.unify [] scrut' (pat2Term pat)
            Env.extendCtxs (promote <$> (decls ++ decls')) $ checkType body ty'

            return ()
      let pats = map (\(Match bnd) -> fst (unsafeUnbind bnd)) alts
      mapM_ checkAlt alts
      exhaustivityCheck scrut' sty pats

    -- c-infer
    _ -> do
      tyA <- inferType tm
      Equal.equate tyA ty'

---------------------------------------------------------------------
-- helper functions for datatypes

-- | type check a list of data constructor arguments against a telescope
tcArgTele :: [Arg] -> [Entry] -> TcMonad ()
tcArgTele [] [] = return ()
tcArgTele args (Def x ty : tele) = do
  -- ensure that the equality is provable at this point
  Equal.equate (Var x) ty
  tcArgTele args tele
tcArgTele (Arg ep1 tm : terms) (Decl (TypeDecl x ep2 ty) : tele)
  | ep1 == ep2 = do
      Env.withStage ep1 $ checkType tm ty
      tele' <- doSubst [(x, tm)] tele
      tcArgTele terms tele'
  | otherwise =
      Env.err
        [ DS $ show ep1,
          DS "argument provided when",
          DS $ show ep2,
          DS "argument was expected"
        ]
tcArgTele [] _ =
  Env.err [DS "Too few arguments provided."]
tcArgTele _ [] =
  Env.err [DS "Too many arguments provided."]

-- | Substitute a list of terms for the variables bound in a telescope
-- This is used to instantiate the parameters of a data constructor
-- to find the types of its arguments.
-- The first argument should only contain 'Rel' type declarations.
substTele :: [Entry] -> [Arg] -> [Entry] -> TcMonad [Entry]
substTele tele args = doSubst (mkSubst tele (map unArg args))
  where
    mkSubst [] [] = []
    mkSubst (Decl (TypeDecl x Rel _) : tele') (tm : tms) =
      (x, tm) : mkSubst tele' tms
    mkSubst _ _ = error "Internal error: substTele given illegal arguments"

-- Propagate the given substitution through the telescope, potentially
-- reworking the constraints
doSubst :: [(TName, Term)] -> [Entry] -> TcMonad [Entry]
doSubst ss [] = return []
doSubst ss (Def x ty : tele') = do
  let tx' = Unbound.substs ss (Var x)
  let ty' = Unbound.substs ss ty
  decls1 <- Equal.unify [] tx' ty'
  decls2 <- Env.extendCtxs (promote <$> decls1) (doSubst ss tele')
  return (decls1 ++ decls2)
doSubst ss (Decl decl : tele') = do
  tynf <- Equal.whnf (Unbound.substs ss (declType decl))
  let decl' = decl {declType = tynf}
  tele'' <- doSubst ss tele'
  return $ Decl decl' : tele''

-----------------------------------------------------------

-- | Create a binding for each of the variables in the pattern
declarePat :: Pattern -> Epsilon -> Type -> TcMonad [Entry]
declarePat (PatVar x) ep ty = return [Decl (TypeDecl x ep ty)]
declarePat (PatCon dc pats) Rel ty = do
  (tc, params) <- Equal.ensureTCon ty
  (Telescope delta, Telescope deltai) <- Env.lookupDCon dc tc
  tele <- substTele delta params deltai
  declarePats dc pats tele
declarePat pat Irr _ty =
  Env.err [DS "Cannot pattern match irrelevant arguments in pattern", DN pat]

-- | Given a list of pattern arguments and a telescope, create a binding for
-- each of the variables in the pattern,
declarePats :: DataConName -> [(Pattern, Epsilon)] -> [Entry] -> TcMonad [Entry]
declarePats dc pats (Def x ty : tele) = do
  let ds1 = [Def x ty]
  ds2 <- Env.extendCtxs (promote <$> ds1) $ declarePats dc pats tele
  return (ds1 ++ ds2)
declarePats dc ((pat, _) : pats) (Decl (TypeDecl x ep ty) : tele) = do
  ds1 <- declarePat pat ep ty
  let tm = pat2Term pat
  tele' <- doSubst [(x, tm)] tele
  ds2 <- Env.extendCtxs (promote <$> ds1) $ declarePats dc pats tele'
  return (ds1 ++ ds2)
declarePats dc [] [] = return []
declarePats dc [] _ = Env.err [DS "Not enough patterns in match for data constructor", DS dc]
declarePats dc pats [] = Env.err [DS "Too many patterns in match for data constructor", DS dc]

-- | Convert a pattern to a term
pat2Term :: Pattern -> Term
pat2Term (PatVar x) = Var x
pat2Term (PatCon dc pats) = DataCon dc (pats2Terms pats)
  where
    pats2Terms :: [(Pattern, Epsilon)] -> [Arg]
    pats2Terms [] = []
    pats2Terms ((p, ep) : ps) = Arg ep t : ts
      where
        t = pat2Term p
        ts = pats2Terms ps

-- | Check all of the types contained within a telescope
tcTypeTele :: [Entry] -> TcMonad ()
tcTypeTele [] = return ()
tcTypeTele (Def x tm : tl) = do
  ty1 <- Env.withStage Irr $ inferType (Var x)
  Env.withStage Irr $ checkType tm ty1
  let decls = [ModuleDef x tm]
  Env.extendCtxs decls $ tcTypeTele tl
tcTypeTele (Decl decl : tl) = do
  tcType (declType decl)
  Env.extendCtx (ModuleDecl decl) $ tcTypeTele tl

-- tcTypeTele tele =
--   Env.err [DS "Invalid telescope: ", DN tele]

--------------------------------------------------------
-- Using the typechecker for decls and modules and stuff
--------------------------------------------------------

-- | Typecheck a collection of modules. Assumes that each module
-- appears after its dependencies. Returns the same list of modules
-- with each definition typechecked
tcModules :: [Module] -> TcMonad [Module]
tcModules = foldM tcM []
  where
    -- Check module m against modules in defs, then add m to the list.
    defs `tcM` m = do
      -- "M" is for "Module" not "monad"
      let name = moduleName m
      tell $ List.singleton $ Info $ "Checking module " ++ show name
      m' <- defs `tcModule` m
      return $ defs ++ [m']

-- | Typecheck an entire module.
tcModule ::
  -- | List of already checked modules (including their entries).
  [Module] ->
  -- | Module to check.
  Module ->
  -- | The same module with all entries checked and elaborated.
  TcMonad Module
tcModule defs m' = do
  checkedEntries <-
    Env.extendCtxMods importedModules $
      foldr
        tcE
        (return [])
        (moduleEntries m')
  return $ m' {moduleEntries = checkedEntries}
  where
    d `tcE` m = do
      -- Extend the Env per the current Entry before checking
      -- subsequent entries.
      x <- tcEntry d
      case x of
        AddHint hint -> Env.extendHints hint m
        -- Add decls to the entries to be returned
        AddCtx decls -> (decls ++) <$> Env.extendCtxsGlobal decls m
    -- Get all of the defs from imported modules (this is the env to check current module in)
    importedModules = filter (\x -> ModuleImport (moduleName x) `elem` moduleImports m') defs

-- | The Env-delta returned when type-checking a top-level Entry.
data HintOrCtx
  = AddHint TypeDecl
  | AddCtx [ModuleEntry]

-- | Check each sort of declaration in a module
tcEntry :: ModuleEntry -> TcMonad HintOrCtx
tcEntry (ModuleDef n term) = do
  oldDef <- Env.lookupDef n
  maybe tc die oldDef
  where
    tc = do
      lkup <- Env.lookupHint n
      case lkup of
        Nothing -> do
          ty <- inferType term
          return $ AddCtx [ModuleDecl (TypeDecl n Rel ty), ModuleDef n term]
        Just decl -> do
          Env.extendCtx (ModuleDecl decl) (checkType term (declType decl))
            `Env.extendErr` [ DS "When checking the term",
                              DN term,
                              DS "against the type",
                              DN (ModuleDecl decl)
                            ]
          return $ AddCtx [ModuleDecl decl, ModuleDef n term]
    die term' =
      Env.extendSourceLocation (unPosFlaky term) (NameResolution.nominalize term) $
        Env.err
          [ DS "Multiple definitions of",
            DN n,
            DS "Previous definition was",
            DN term'
          ]
tcEntry (ModuleDecl decl) = do
  duplicateTypeBindingCheck decl
  tcType (declType decl)
  return $ AddHint decl
tcEntry (Demote ep) = return (AddCtx [Demote ep])

-- rule Entry_data
tcEntry (ModuleData t (Telescope delta) cs) =
  do
    -- Check that the telescope for the datatype definition is well-formed
    edelta <- tcTypeTele delta
    ---- check that the telescope provided
    ---  for each data constructor is wellfomed, and elaborate them
    let elabConstructorDef defn@(ConstructorDef pos d (Telescope tele)) =
          Env.extendSourceLocation pos (NameResolution.nominalize defn) $
            Env.extendCtx (ModuleData t (Telescope delta) []) $
              Env.extendCtxTele (promote <$> delta) $ do
                etele <- tcTypeTele tele
                return (ConstructorDef pos d (Telescope tele))
    ecs <- mapM elabConstructorDef cs
    -- Implicitly, we expect the constructors to actually be different...
    let cnames = map (\(ConstructorDef _ c _) -> c) cs
    unless (length cnames == length (nub cnames)) $
      Env.err [DS "Datatype definition", DS t, DS "contains duplicated constructors"]
    -- finally, add the datatype to the env and perform action m
    return $ AddCtx [ModuleData t (Telescope delta) ecs]

-- | Make sure that we don't have the same name twice in the
-- environment. (We don't rename top-level module definitions.)
duplicateTypeBindingCheck :: TypeDecl -> TcMonad ()
duplicateTypeBindingCheck decl = do
  -- Look for existing type bindings ...
  let n = declName decl
  l <- Env.lookupTyMaybe n
  l' <- Env.lookupHint n
  -- ... we don't care which, if either are Just.
  case catMaybes [l, l'] of
    [] -> return ()
    -- We already have a type in the environment so fail.
    decl' : _ ->
      let p = unPosFlaky $ declType decl
          msg =
            [ DS "Duplicate type declaration",
              DN (ModuleDecl decl),
              DS "Previous was",
              DN (ModuleDecl decl')
            ]
       in Env.extendSourceLocation p (NameResolution.nominalize (ModuleDecl decl)) $ Env.err msg

-----------------------------------------------------------
-- Checking that pattern matching is exhaustive
-----------------------------------------------------------

-- | Given a particular type and a list of patterns, make
-- sure that the patterns cover all potential cases for that
-- type.
-- If the list of patterns starts with a variable, then it doesn't
-- matter what the type is, the variable is exhaustive. (This code
-- does not report unreachable patterns.)
-- Otherwise, the scrutinee type must be a type constructor, so the
-- code looks up the data constructors for that type and makes sure that
-- there are patterns for each one.
exhaustivityCheck :: Term -> Type -> [Pattern] -> TcMonad ()
exhaustivityCheck scrut ty (PatVar x : _) = return ()
exhaustivityCheck scrut ty pats = do
  (tcon, tys) <- Equal.ensureTCon ty
  (Telescope delta, mdefs) <- Env.lookupTCon tcon
  case mdefs of
    Just datacons -> do
      loop pats datacons
      where
        loop [] [] = return ()
        loop [] dcons = do
          l <- checkImpossible dcons
          if null l
            then return ()
            else Env.err $ DS "Missing case for" : map DS l
        loop (PatVar x : _) dcons = return ()
        loop (PatCon dc args : pats') dcons = do
          (ConstructorDef _ _ (Telescope tele), dcons') <- removeDCon dc dcons
          tele' <- substTele delta tys tele
          let (aargs, pats'') = relatedPats dc pats'
          -- check the arguments of the data constructor
          checkSubPats dc tele' (args : aargs)
          loop pats'' dcons'

        -- make sure that the given list of constructors is impossible
        -- in the current environment
        checkImpossible :: [ConstructorDef] -> TcMonad [DataConName]
        checkImpossible [] = return []
        checkImpossible (ConstructorDef _ dc (Telescope tele) : rest) = do
          this <-
            ( do
                tele' <- substTele delta tys tele
                tcTypeTele tele'
                return [dc]
              )
              `catchError` (\_ -> return [])
          others <- checkImpossible rest
          return (this ++ others)
    Nothing ->
      Env.err [DS "Cannot determine constructors of", DN ty]

-- | Given a particular data constructor name and a list of data
-- constructor definitions, pull the definition out of the list and
-- return it paired with the remainder of the list.
removeDCon ::
  DataConName ->
  [ConstructorDef] ->
  TcMonad (ConstructorDef, [ConstructorDef])
removeDCon dc (cd@(ConstructorDef _ dc' _) : rest)
  | dc == dc' =
      return (cd, rest)
removeDCon dc (cd1 : rest) = do
  (cd2, rr) <- removeDCon dc rest
  return (cd2, cd1 : rr)
removeDCon dc [] = Env.err [DS $ "Internal error: Can't find " ++ show dc]

-- | Given a particular data constructor name and a list of patterns,
-- pull out the subpatterns that occur as arguments to that data
-- constructor and return them paired with the remaining patterns.
relatedPats :: DataConName -> [Pattern] -> ([[(Pattern, Epsilon)]], [Pattern])
relatedPats dc [] = ([], [])
relatedPats dc (pc@(PatVar _) : pats) = ([], pc : pats)
relatedPats dc ((PatCon dc' args) : pats)
  | dc == dc' =
      let (aargs, rest) = relatedPats dc pats
       in (args : aargs, rest)
relatedPats dc (pc : pats) =
  let (aargs, rest) = relatedPats dc pats
   in (aargs, pc : rest)

-- | Occurs check for the subpatterns of a data constructor. Given
-- the telescope specifying the types of the arguments, plus the
-- subpatterns identified by relatedPats, check that they are each
-- exhaustive.

-- for simplicity, this function requires that all subpatterns
-- are pattern variables.
checkSubPats :: DataConName -> [Entry] -> [[(Pattern, Epsilon)]] -> TcMonad ()
checkSubPats dc [] _ = return ()
checkSubPats dc (Def _ _ : tele) patss = checkSubPats dc tele patss
checkSubPats dc (Decl _ : tele) patss
  | (not . null) patss && not (any null patss) = do
      let hds = map (fst . head) patss
      let tls = map tail patss
      case hds of
        [PatVar _] -> checkSubPats dc tele tls
        _ -> Env.err [DS "All subpatterns must be variables in this version."]
checkSubPats dc t ps =
  Env.err [DS "Internal error in checkSubPats", DS dc, DS (show ps)]
