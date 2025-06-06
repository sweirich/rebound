{-# LANGUAGE ViewPatterns #-}

module PiForall.Rebound.TypeCheck (tcModules, inferType, checkType) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Writer (tell)
import Data.Fin qualified as Fin
import Data.Foldable
import Data.List (nub)
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Maybe (catMaybes)
import Data.Proxy (Proxy (..))
import Data.SNat qualified as SNat
import Data.Vec qualified as Vec
import PiForall.Log qualified as Log
import PiForall.PrettyPrint (Display (..), disp, pp)
import PiForall.Rebound.Environment (Context, D (..), TcMonad)
import PiForall.Rebound.Environment qualified as Env
import PiForall.Rebound.Equal qualified as Equal
import PiForall.Rebound.ScopeCheck (Some1 (..))
import PiForall.Rebound.Syntax
import Prettyprinter (pretty)
import Rebound
import Rebound.Bind.Local qualified as Local
import Rebound.Bind.Pat (PatList (..))
import Rebound.Bind.Pat qualified as Pat
import Rebound.Bind.Scoped (TeleList (..), (<++>), (<:>))
import Rebound.Bind.Scoped qualified as Scoped
import Rebound.Bind.Single qualified as B
import Rebound.Context
import Rebound.Context qualified as Context
import Rebound.Lib
import Rebound.MonadScoped qualified as Scope
import Unsafe.Coerce qualified

---------------------------------------------------------------------

-- | Infer/synthesize the type of a term
inferType :: forall n. Term n -> TcMonad n (Typ n)
inferType a = case a of
  -- i-var
  (Var x) -> Env.lookupTy x
  (Global n) -> Env.lookupGlobalTy n
  -- i-type
  TyType -> return TyType
  -- i-pi
  (Pi tyA bnd) -> do
    tcType tyA
    let (x, tyB) = Local.unbindl bnd
    Env.push1 x tyA $ tcType tyB
    return TyType

  -- i-app
  (App a b) -> do
    ty1 <- inferType a
    (tyA, bnd) <- Equal.ensurePi ty1
    checkType b tyA
    return (Local.instantiate bnd b)

  -- i-ann
  (Ann a tyA) -> do
    tcType tyA
    checkType a tyA
    return tyA

  -- Practicalities
  -- remember the current position in the type checking monad
  (Pos p a) ->
    Env.extendSourceLocation p a $ inferType a
  -- Type constructor application
  tm@(TyCon c params) -> do
    (DataDef delta _ cs) <- Env.lookupTCon c
    unless (length params == toInt (Scoped.scopedSize delta)) $
      Env.err
        [ DS "Datatype constructor",
          DS c,
          DS ("should have " ++ show (Scoped.scopedSize delta) ++ " parameters, but was given"),
          DC (length params)
        ]
    let delta' = weakenTeleClosed delta
    tcArgTele params delta'
    return TyType

  -- Data constructor application
  -- we don't know the expected type, so see if there
  -- is only one datacon of that name that takes no
  -- parameters
  (DataCon c args) -> do
    matches <- Env.lookupDConAll c
    case matches of
      [ ( tname,
          ScopedConstructorDef
            TNil
            (ConstructorDef _ (thetai :: Telescope m Z))
          )
        ] -> do
          let numArgs = toInt $ Scoped.scopedSize thetai
          unless (length args == numArgs) $
            Env.err
              [ DS "Constructor",
                DS c,
                DS "should have",
                DC numArgs,
                DS "data arguments, but was given",
                DC (length args),
                DS "arguments."
              ]
          let thetai' = weakenTeleClosed thetai
          tcArgTele args thetai'
          return $ TyCon tname []
      [_] ->
        Env.err
          [ DS "Cannot infer the parameters to data constructors.",
            DS "Add an annotation."
          ]
      _ -> Env.err [DS "Ambiguous data constructor", DC c]
  (TyEq a b) -> do
    aTy <- inferType a
    checkType b aTy
    return TyType

  -- cannot synthesize the type of the term
  _ ->
    Env.err [DS "Must have a type annotation for", DU a]

-------------------------------------------------------------------------

-- | Make sure that the term is a "type" (i.e. that it has type 'Type')
tcType :: Term n -> TcMonad n ()
tcType tm = checkType tm TyType

-------------------------------------------------------------------------

-- | Check that the given term has the expected type
checkType :: forall n. Term n -> Typ n -> TcMonad n ()
checkType tm ty = do
  ty' <- Equal.whnf ty
  case tm of
    -- c-lam: check the type of a function
    (Lam bnd) -> do
      (tyA, bnd2) <- Equal.ensurePi ty
      let (x, body) = Local.unbindl bnd
      -- unbind the variables in the lambda expression and pi type
      let tyB = Local.getBody bnd2
      -- check the type of the body of the lambda expression
      Env.push1 x tyA $ checkType body tyB

    -- Practicalities
    (Pos p a) ->
      Env.extendSourceLocation p a $ checkType a ty'
    TrustMe -> return ()
    PrintMe -> do
      c <- Env.displayContext
      r <- Env.displayRefinement
      Env.err
        [ DS "Unmet obligation.\nContext:",
          c,
          DS "\nRefinements",
          r,
          DS "\nGoal:",
          DU ty'
        ]
    (Let a bnd) -> do
      let (x, b) = Local.unbindl bnd
      tyA <- inferType a
      -- Shift the right-hand-side into the extended scope
      let ty'' = applyE @Term shift1E ty'
      let a' = applyE @Term shift1E a
      Env.withScopeSize $
        -- Add binding to scope
        -- Add binding to scope
        -- Add binding to scope
        -- Add binding to scope

        -- Add binding to scope
        Env.push1 x tyA $
          -- Remember the (definitional) equality
          -- Remember the (definitional) equality
          -- Remember the (definitional) equality
          -- Remember the (definitional) equality

          -- Remember the (definitional) equality
          Equal.pushRefinement FZ a' $
            checkType b ty''
    TmRefl -> do
      (a, b) <- Equal.ensureEq ty
      Equal.equate a b

    -- c-subst
    tm@(Subst a b) -> Env.withScopeSize $ do
      -- infer the type of the proof 'b'
      tp <- inferType b
      -- make sure that it is an equality between some m and n
      (m, n) <- Equal.ensureEq tp

      -- if either side is a variable, add a definition to the context
      -- if this fails, then the user should use contra instead
      edecl <- Equal.unify False m n
      -- if proof is a variable, add a definition to the context
      pdecl <- Equal.unify False b TmRefl
      -- I don't think this join can fail, but we have to check
      r' <-
        -- fromRefinement <$>
        joinR edecl pdecl
          `Env.whenNothing` [DS "incompatible equality in subst"]
      Equal.pushRefinements r' $ checkType a ty'

    -- c-contra
    (Contra p) -> do
      ty' <- inferType p
      (a, b) <- Equal.ensureEq ty'
      a' <- Equal.whnf a
      b' <- Equal.whnf b
      case (a', b') of
        (DataCon da _, DataCon db _)
          | da /= db ->
              return ()
        (_, _) ->
          Env.err
            [ DS "I can't tell that",
              DU a',
              DS "and",
              DU b',
              DS "are contradictory"
            ]

    -- c-data
    -- we know the expected type of the data constructor
    -- so look up its type in the context
    (DataCon c args) -> do
      case ty' of
        (TyCon tname params) -> do
          ScopedConstructorDef (delta :: Telescope p Z) (ConstructorDef cn (theta :: Telescope p' p)) <- Env.lookupDCon c tname
          let numArgs = toInt $ Scoped.scopedSize theta
          unless (length args == numArgs) $
            Env.err
              [ DS "Constructor",
                DS c,
                DS "should have",
                DC numArgs,
                DS "data arguments, but was given",
                DC (length args),
                DS "arguments."
              ]
          newTele <- substTele True delta params theta
          tcArgTele args newTele
        _ ->
          Env.err [DS "Unexpected type", DU ty', DS "for data constructor", DU tm]
    (Case scrut alts) -> do
      sty <- inferType scrut
      (c, args) <- Equal.ensureTCon sty
      mapM_ (checkAlt c args) alts
      exhaustivityCheck scrut sty (map getSomePat alts)
      where
        checkAlt :: TyConName -> [Term n] -> Match n -> TcMonad n ()
        checkAlt c args (Branch bnd) = Env.withScopeSize $ Pat.unbind bnd $ \pat body -> do
          let p = size pat
          -- shift scrutinee and result type into the scope of the branch
          let scrut'' = applyE @Term (shiftNE p) scrut
          let ty'' = applyE @Term (shiftNE p) ty'

          -- add variables from pattern to context
          (pat, tm', rPat) <- declarePat pat (TyCon c args)
          Env.push pat $ do
            -- compare scrutinee and pattern: fails if branch is inaccessible
            rScrut <- Equal.unify False scrut'' tm'

            r <-
              withSNat
                (sPlus p (snat @n))
                $ joinR rPat rScrut `Env.whenNothing` [DS "cannot join refinements"]
            Equal.pushRefinements r $ checkType body ty''

    -- c-infer
    _ -> do
      tyA <- inferType tm
      Equal.equate tyA ty'

getSomePat :: Match n -> Some1 Pattern
getSomePat (Branch bnd) = Some1 (Pat.getPat bnd)

---------------------------------------------------------------------
-- type checking datatype definitions, type constructor applications and
-- data constructor applications
---------------------------------------------------------------------

-- | Check all of the types contained within a telescope
tcTypeTele ::
  forall p1 n.
  Telescope p1 n ->
  TcMonad n ()
tcTypeTele TNil = return ()
tcTypeTele (TCons (LocalDef x tm) (tele :: Telescope p2 n)) = do
  ty1 <- inferType (Var x)
  checkType tm ty1
  Env.withScopeSize $ Equal.pushRefinement x tm $ tcTypeTele tele
tcTypeTele (TCons (LocalDecl x ty) (tl :: Telescope p2 (S n))) = do
  tcType ty
  Env.push1 x ty $ tcTypeTele tl

-- | type check a list of data constructor arguments against a telescope,
-- returning a substitution for each of the variables bound in the
-- telescope, plus a refinement for variables currently in scope
tcArgTele ::
  forall p n.
  [Term n] ->
  Telescope p n ->
  TcMonad n ()
tcArgTele [] TNil = return ()
tcArgTele [] _ = Env.err [DS "Too few arguments provided."]
tcArgTele _ TNil = Env.err [DS "Too many arguments provided."]
tcArgTele args (TCons (LocalDef x ty) (tele :: Telescope p2 n)) = do
  -- ensure that the equality is provable at this point
  Equal.equate (Var x) ty
  tcArgTele args tele
tcArgTele (tm : terms) (TCons (LocalDecl ln ty) (tele :: Telescope p2 (S n))) = do
  checkType tm ty
  -- Using best-effort would be unsound, as constructors could be
  -- instantiated without proving that the equality they require are
  -- satisfied.
  tele' <- doSubst @N1 True (tm .: idE) tele
  tcArgTele terms tele'

-- | Make a substitution from a list of arguments.
-- Checks that the length is as specified, and fails
-- otherwise
mkSubst ::
  forall p n.
  [Term n] ->
  SNat p ->
  TcMonad n (Env Term (p + n) n)
mkSubst [] SZ = return idE
mkSubst (tm : tms) (snat_ -> SS_ m) = do
  ss <- mkSubst tms m
  return $ tm .: ss
mkSubst [] _ = Env.err [DS "Too few arguments provided."]
mkSubst _ SZ = Env.err [DS "Too many arguments provided."]

-- Iterate over the list in result
mkSubst' :: forall p n. [Term n] -> SNat p -> TcMonad n (Env Term (p + n) n)
mkSubst' args p = do
  (rargs, r) <- go p
  case rargs of
    [] -> return r
    _ -> Env.err [DS "Too many arguments provided."]
  where
    go :: forall p. SNat p -> TcMonad n ([Term n], Env Term (p + n) n)
    go SZ = return (args, idE)
    go (snat_ -> SS_ m) = do
      (rargs, ss) <- go m
      case rargs of
        (tm : tms) -> return (tms, tm .: ss)
        [] -> Env.err [DS "Too few arguments provided"]

-- | Substitute a list of terms for the variables bound in a telescope
-- This is used to instantiate the parameters of a data constructor
-- to find the types of its arguments.
-- p1 : number of variables in delta
-- p2 : number of variables in thetai
-- delta: the type-level telescope (i.e. the telescope being instantiated)
-- params: parameters used to instantiate delta
-- theta: the constructor level telescope (i.e. the telescope in which the subst. happens)
-- This could fail if any constraints are not satisfiable.
substTele ::
  forall p1 p2 n.
  Bool ->
  Telescope p1 Z -> -- delta
  [Term n] -> -- params
  Telescope p2 p1 -> -- theta
  TcMonad n (Telescope p2 n)
substTele strict delta params theta =
  do
    (e :: Env Term (p1 + n) n) <-
      mkSubst' params (Scoped.scopedSize delta)
    ss <- Env.scopeSize
    let weaken :: Env Term p1 (p1 + n)
        weaken = withSNat (size delta) $ weakenER ss
    let theta' :: Telescope p2 (p1 + n)
        theta' = applyE @Term weaken theta
    doSubst @p1 strict e theta'

-- Propagate the given substitution through a telescope, potentially
-- reworking the constraints

doSubst :: forall q n p. Bool -> Env Term (q + n) n -> Telescope p (q + n) -> TcMonad n (Telescope p n)
doSubst strict = doSubstRec @q @n strict s0

-- we need to generalize the recursion so that we can increase the scope as we traverse the telescope
doSubstRec :: forall q n k p. Bool -> SNat k -> Env Term ((k + q) + n) (k + n) -> Telescope p ((k + q) + n) -> TcMonad (k + n) (Telescope p (k + n))
doSubstRec _ k r TNil = return Scoped.nil
doSubstRec strict k r (TCons e (t :: Telescope p2 m)) = case e of
  LocalDef x (tm :: Term ((k + q) + n)) -> case axiomPlusZ @p2 of
    Refl -> do
      let tx' :: Term (k + n)
          tx' = applyE r (Var x)
      let tm' :: Term (k + n)
          tm' = applyE r tm
      defs :: Refinement Term (k + n) <- Equal.unify strict tx' tm'
      (tele' :: Telescope p2 (k + n)) <- doSubstRec @q @n strict k r t
      return $ appendDefs defs tele'
  LocalDecl nm (ty :: Term ((k + q) + n)) -> do
    let ty' :: Term (k + n)
        ty' = applyE r ty
    t' <- Env.push1 nm ty' $ doSubstRec @q @n strict (SNat.next k) (up r) t
    return $ LocalDecl nm ty' <:> t'

appendDefs :: Refinement Term n -> Telescope p n -> Telescope p n
appendDefs (Refinement m) = go (Map.toList m)
  where
    go :: forall n p. [(Fin n, Term n)] -> Telescope p n -> Telescope p n
    go [] t = t
    go ((x, tm) : defs) (t :: Telescope p1 n) = case axiomPlusZ @p1 of Refl -> LocalDef x tm <:> (go defs t)

-- | Create a binding for each of the variables in the pattern, producing an extended context and
-- a term corresponding to the variables
declarePat ::
  forall p n.
  Pattern p ->
  Typ n ->
  TcMonad n (Telescope p n, Term (p + n), Refinement Term (p + n))
declarePat (PatVar x) ty = do
  pure (LocalDecl x ty <:> Scoped.nil, Var Fin.f0, emptyR)
declarePat p@(PatCon dc (pats :: PatList Pattern p)) ty = do
  (tc, params) <- Equal.ensureTCon ty
  ScopedConstructorDef (delta :: Telescope p1 'Z) (ConstructorDef cn (thetai :: Telescope p2 p1)) <- Env.lookupDCon dc tc
  if Pat.lengthPL pats == toInt (Scoped.scopedSize thetai)
    then do
      (tele :: Telescope p2 n) <- substTele False delta params thetai
      (defs, tms', r) <- declarePats pats tele
      pure (defs, DataCon dc tms', r)
    else Env.err [DS "Wrong number of arguments to data constructor", DC cn]

-- | Given a list of pattern arguments and a telescope, create a binding for
-- each of the variables in the pattern, the term form of the pattern, and a refinement
-- from the constraints
-- p is the number of variables bound in the pattern list
-- pt is the length of the pattern list
-- n is the current scope
declarePats ::
  forall p pt n.
  PatList Pattern p ->
  Telescope pt n ->
  TcMonad n (Telescope p n, [Term (p + n)], Refinement Term (p + n))
declarePats pats (TCons (LocalDef x ty) (tele :: Telescope p1 n)) = do
  let r0 = singletonR (x, ty)
  ss <- Env.scopeSize
  tele' <- withSNat ss $ doSubst @Z False (fromRefinement r0) tele
  (defs, tms', rf) <- declarePats pats tele'
  let r1 = shift (size pats) r0
  r' <-
    withSNat (sPlus (size pats) ss) $
      joinR r1 rf `Env.whenNothing` [DS "Cannot create refinement"]
  pure (defs, tms', r')
declarePats
  (PCons (p1 :: Pattern p1) (p2 :: PatList Pattern p2))
  (TCons (LocalDecl x ty1) (tele2 :: Telescope p3 (S n))) =
    do
      let fact :: p2 + (p1 + n) :~: p + n
          fact = axiomAssoc @p2 @p1 @n
      case fact of
        Refl -> do
          (defs1, tm :: Term (p1 + n), rf1 :: Refinement Term (p1 + n)) <- declarePat @p1 p1 ty1
          s <- Env.scopeSize
          let sp1 = size p1
          let ss :: Env Term (S n) (p1 + n)
              ss = Scoped.instantiateWeakenEnv sp1 s tm
          let tele' :: Telescope p3 (p1 + n)
              tele' = applyE ss tele2
          (defs2, tms :: [Term (p2 + (p1 + n))], rf2 :: Refinement Term (p2 + (p1 + n))) <- Env.push defs1 $ declarePats @p2 @p3 @(p1 + n) p2 tele'
          let sp2 = size p2
          let ctx = defs1 <++> defs2
          case withSNat (sPlus sp2 (sPlus sp1 s)) $ joinR (shift (size p2) rf1) rf2 of
            Just rf -> return (ctx, applyE @Term (shiftNE (size p2)) tm : tms, rf)
            Nothing -> Env.err [DS "cannot create refinement"]
declarePats PNil TNil = return (TNil, [], emptyR)
declarePats PNil _ = Env.err [DS "Not enough patterns in match for data constructor"]
declarePats _ TNil = Env.err [DS "Too many patterns in match for data constructor"]

--------------------------------------------------------
-- Using the typechecker for decls and modules and stuff
--------------------------------------------------------

-- | Typecheck a collection of modules. Assumes that each module
-- appears after its dependencies. Returns the same list of modules
-- with each definition typechecked
tcModules :: [Module] -> TcMonad Z [Module]
tcModules = foldM tcM []
  where
    -- Check module m against modules in defs, then add m to the list.
    defs `tcM` m = do
      -- "M" is for "Module" not "monad"
      let name = moduleName m
      tell $ List.singleton $ Log.Info $ "Checking module " ++ show name
      m' <- defs `tcModule` m
      return $ defs ++ [m']

-- | Typecheck an entire module.
tcModule ::
  -- | List of already checked modules (including their entries).
  [Module] ->
  -- | Module to check.
  Module ->
  -- | The same module with all entries checked and elaborated.
  TcMonad Z Module
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
        AddHint x hint -> Env.extendHints (x, hint) m
        -- Add decls to the entries to be returned
        AddCtx decls -> (decls ++) <$> Env.extendCtxs decls m
    -- Get all of the defs from imported modules (this is the env to check current module in)
    importedModules = filter (\x -> ModuleImport (moduleName x) `elem` moduleImports m') defs

-- | The Env-delta returned when type-checking a top-level Entry.
data HintOrCtx
  = AddHint GlobalName (Typ Z)
  | AddCtx [ModuleEntry]

-- | Check each sort of declaration in a module
tcEntry :: ModuleEntry -> TcMonad Z HintOrCtx
tcEntry (ModuleDef n term) =
  do
    r <- Env.ensureError $ Env.lookupGlobalDef n
    case r of
      Left _ -> do
        lkup <- Env.lookupHint n
        case lkup of
          Nothing -> do
            ty <- inferType term
            return $ AddCtx [ModuleDecl n ty, ModuleDef n term]
          Just ty -> do
            let decl = ModuleDecl n ty
            Env.extendCtx decl (checkType term ty)
              `Env.extendErr` [ DS "When checking the term",
                                DU term,
                                DS "against the type",
                                DZ decl
                              ]
            return (AddCtx [decl, ModuleDef n term])
      Right term' ->
        Env.extendSourceLocation
          (unPosFlaky term)
          term
          ( Env.err
              [ DS "Multiple definitions of",
                DC n,
                DS "Previous definition was",
                DU term'
              ]
          )
tcEntry decl@(ModuleDecl x ty) = do
  duplicateTypeBindingCheck decl
  tcType ty
  return (AddHint x ty)
    `Env.extendErr` [ DS "when checking the type declaration",
                      DS x,
                      DS ":",
                      DU ty
                    ]
-- rule Entry_data
tcEntry decl@(ModuleData n (DataDef (delta :: Telescope n Z) s cs)) =
  ( case axiomPlusZ @n of
      Refl -> do
        -- Implicitly, we expect the constructors to actually be different...
        let cnames = map (\(ConstructorDef c _) -> c) cs
        unless (length cnames == length (nub cnames)) $
          Env.err
            [DS "Datatype definition", DC n, DS "contains duplicated constructors"]
        -- Check that the telescope for the datatype definition is well-formed
        tcTypeTele delta
        -- check that the telescope provided
        -- for each data constructor is wellfomed, and elaborate them
        Env.push delta $
          Env.extendCtx (ModuleData n (DataDef delta s [])) $
            mapM_ checkConstructorDef cs
        return (AddCtx [decl])
  )
    `Env.extendErr` [DS "when checking the datatype declaration", DZ decl]
  where
    checkConstructorDef defn@(ConstructorDef _ theta) =
      tcTypeTele theta
        `Env.extendErr` [ DS "when checking the constructor declaration",
                          DU defn
                        ]
tcEntry (ModuleFail failing) = do
  r <- Env.ensureError (tcEntry failing)
  case r of
    Left _ -> return $ AddCtx []
    Right _ -> Env.err [DS "Statement", DZ failing, DS "should fail to typecheck, but succeeded."]

-- | Make sure that we don't have the same name twice in the
-- environment. (We don't rename top-level module definitions.)
duplicateTypeBindingCheck :: ModuleEntry -> TcMonad Z ()
duplicateTypeBindingCheck decl = do
  -- Look for existing type bindings ...
  let n = declName decl
  l <- (Just <$> Env.lookupGlobalTy n) `catchError` \_ -> return Nothing
  l' <- Env.lookupHint n
  -- ... we don't care which, if either are Just.
  case catMaybes [l, l'] of
    [] -> return ()
    -- We already have a type in the environment so fail.
    decl' : _ ->
      let p = unPosFlaky $ declType decl
          msg =
            [ DS "Duplicate type declaration",
              DZ decl,
              DS "Previous was",
              DU decl'
            ]
       in Env.extendSourceLocation p decl $ Env.err msg

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
exhaustivityCheck :: forall n. Term n -> Typ n -> [Some1 Pattern] -> TcMonad n ()
exhaustivityCheck scrut ty (Some1 (PatVar x) : _) = return ()
exhaustivityCheck scrut ty pats = do
  (tcon, tys) <- Equal.ensureTCon ty
  DataDef (delta :: Telescope p1 Z) sort datacons <- Env.lookupTCon tcon
  let loop :: [Some1 Pattern] -> [ConstructorDef p1] -> TcMonad n ()
      loop [] [] = return ()
      loop [] dcons = do
        l <- checkImpossible dcons
        if null l
          then return ()
          else Env.err $ DS "Missing case for" : map DC l
      loop (Some1 (PatVar x) : _) dcons = return ()
      loop (Some1 (PatCon dc (args :: PatList Pattern p)) : pats') dcons = do
        (ConstructorDef _ (tele :: Telescope p2 p1), dcons') <- removeDCon dc dcons
        tele' <- substTele False delta tys tele
        let (aargs, pats'') = relatedPats dc pats'
        -- check the arguments of the data constructor together with
        -- all other related argument lists
        checkSubPats dc tele' (Some1 args : aargs)
        loop pats'' dcons'

      -- make sure that the given list of constructors is impossible
      -- in the current environment
      checkImpossible :: [ConstructorDef p1] -> TcMonad n [DataConName]
      checkImpossible [] = return []
      checkImpossible (ConstructorDef dc tele : rest) = do
        scrut' <- Equal.whnf scrut
        this <-
          ( do
              -- Strict mode would definitely be unsound here
              tele' <- substTele False delta tys tele
              tcTypeTele tele'
              case scrut' of
                DataCon dc' _ | dc /= dc' -> return []
                _ -> return [dc]
            )
            `catchError` (\_ -> return [])
        others <- checkImpossible rest
        return (this ++ others)
  loop pats datacons

-- | Given a particular data constructor name and a list of data
-- constructor definitions, pull the definition out of the list and
-- return it paired with the remainder of the list.
removeDCon ::
  DataConName ->
  [ConstructorDef p1] ->
  TcMonad n (ConstructorDef p1, [ConstructorDef p1])
removeDCon dc (cd@(ConstructorDef dc' _) : rest)
  | dc == dc' =
      return (cd, rest)
removeDCon dc (cd1 : rest) = do
  (cd2, rr) <- removeDCon dc rest
  return (cd2, cd1 : rr)
removeDCon dc [] = Env.err [DS $ "Internal error: Can't find " ++ show dc]

-- | Given a particular data constructor name and a list of patterns,
-- pull out the subpatterns that occur as arguments to that data
-- constructor and return them paired with the remaining patterns.
relatedPats :: DataConName -> [Some1 Pattern] -> ([Some1 (PatList Pattern)], [Some1 Pattern])
relatedPats dc [] = ([], [])
relatedPats dc (pc@(Some1 (PatVar _)) : pats) = ([], pc : pats)
relatedPats dc (pc@(Some1 (PatCon dc' args)) : pats)
  | dc == dc' =
      let (aargs, rest) = relatedPats dc pats
       in (Some1 args : aargs, rest)
relatedPats dc (pc : pats) =
  let (aargs, rest) = relatedPats dc pats
   in (aargs, pc : rest)

-- | Occurs check for the subpatterns of a data constructor. Given
-- the telescope specifying the types of the arguments, plus the
-- subpatterns identified by relatedPats, check that they are each
-- exhaustive. (This is the PatList version of `exhaustivityCheck`)

-- for simplicity, this function requires that all subpatterns
-- are pattern variables.
checkSubPats :: forall p m n. DataConName -> Telescope p n -> [Some1 (PatList Pattern)] -> TcMonad m ()
checkSubPats dc TNil _ = return ()
checkSubPats dc (TCons (LocalDef _ _) (tele :: Telescope p2 n)) (patss :: [Some1 (PatList Pattern)]) =
  checkSubPats dc tele patss
checkSubPats
  dc
  (TCons (LocalDecl x _) (tele :: Telescope p2 (S n)))
  (patss :: [Some1 (PatList Pattern)]) = do
    case allHeadVars patss of
      Just tls -> checkSubPats dc tele tls
      Nothing -> Env.err [DS "All subpatterns must be variables in this version."]

-- check that the head of each list is a single pattern variable and return all of the
-- tails
allHeadVars :: [Some1 (PatList Pattern)] -> Maybe [Some1 (PatList Pattern)]
allHeadVars [] = Just []
allHeadVars (Some1 (PCons (PatVar x) (pats :: PatList Pattern p2)) : patss) = do
  withSNat (size pats) $
    (Some1 pats :) <$> allHeadVars patss
allHeadVars _ = Nothing