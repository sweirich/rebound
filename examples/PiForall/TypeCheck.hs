module PiForall.TypeCheck (tcModules, inferType, checkType) where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Except


import Data.List (nub)
import Data.Foldable
import Data.Maybe ( catMaybes )
import qualified Data.Map as Map

import PiForall.Environment (TcMonad, Context)
import PiForall.Environment qualified as Env
import PiForall.Equal qualified as Equal
import PiForall.PrettyPrint (Display (..), D(..), disp, pp, debug)
import PiForall.Syntax
import Debug.Trace

import AutoEnv.Lib
import AutoEnv
import AutoEnv.MonadScoped
import qualified AutoEnv.Bind as B
import qualified AutoEnv.Pat.Simple as Pat
import qualified AutoEnv.Pat.Scoped as Scoped
import qualified AutoEnv.Pat.LocalBind as Local
import AutoEnv.Context

import Prettyprinter (pretty)

---------------------------------------------------------------------

-- | Infer/synthesize the type of a term
inferType :: forall n. SNatI n => Term n -> Context n -> TcMonad n (Typ n)
inferType a ctx = case a of
  -- i-var
  (Var x) -> 
    -- Scoped checked, so cannot fail
    pure $ Env.lookupTy x ctx 

  (Global n) -> 
    -- this weakening should be a no-op
    case axiomPlusZ @n of 
      Refl -> weaken' (snat @n) <$> Env.lookupGlobalTy n 
  -- i-type
  TyType -> return TyType

  -- i-pi
  (Pi tyA bnd) -> do
    tcType tyA ctx
    Local.unbind bnd $ \(x,tyB) -> do
      push x (tcType tyB (Env.extendTy tyA ctx))
      return TyType

  -- i-app
  (App a b) -> do
    ty1 <- inferType a ctx
    ty1' <- Equal.whnf ty1 
    case ty1' of 
      (Pi tyA bnd) -> do
          checkType b tyA ctx
          return (Local.instantiate bnd b)
      _ -> Env.err [DS "Expected a function type but found ", DD ty1]

  -- i-ann
  (Ann a tyA) -> do
    tcType tyA ctx
    checkType a tyA ctx
    return tyA
  
  -- Practicalities
  -- remember the current position in the type checking monad
  (Pos p a) ->
    Env.extendSourceLocation p a $ inferType a ctx

  -- Type constructor application
  (TyCon c params) -> do
    (DataDef delta _ cs) <- Env.lookupTCon c
    unless (length params == toInt (Scoped.size delta)) $
      Env.err
        [ DS "Datatype constructor",
          DS c,
          DS ("should have " ++ show (Scoped.size delta) ++ " parameters, but was given"),
          DC (length params)
        ]
    let delta' = applyE @Term (weakenE' (snat :: SNat n)) delta
    case axiomPlusZ @n of 
      Refl -> do
       tcArgTele params delta' ctx
       return TyType

  -- Data constructor application
  -- we don't know the expected type, so see if there
  -- is only one datacon of that name that takes no
  -- parameters
  (DataCon c args) -> do
    matches <- Env.lookupDConAll c
    case matches of
      [ (tname, ScopedConstructorDef 
                    Tele (ConstructorDef _ (thetai :: Telescope m Z))) ] -> do
        let numArgs = toInt $ Scoped.size thetai
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
        case axiomPlusZ @n of
          Refl -> do
            let thetai' = applyE @Term (weakenE' (snat @n)) thetai
            _ <- tcArgTele args thetai' ctx
            return $ TyCon tname []
      [_] ->
        Env.err
          [ DS "Cannot infer the parameters to data constructors.",
            DS "Add an annotation."
          ]
      _ -> Env.err [DS "Ambiguous data constructor", DC c] 

  (TyEq a b) -> do
    aTy <- inferType a ctx
    checkType b aTy ctx
    return TyType 

  -- cannot synthesize the type of the term
  _ -> 
    Env.err [DS "Must have a type annotation for", DD a] 


-------------------------------------------------------------------------

-- | Make sure that the term is a "type" (i.e. that it has type 'Type')
tcType :: SNatI n => Term n -> Context n -> TcMonad n ()
tcType tm = checkType tm TyType

-------------------------------------------------------------------------
-- | Check that the given term has the expected type
checkType :: forall n. SNatI n => Term n -> Typ n -> Context n -> TcMonad n ()
checkType tm ty ctx = do
  ty' <- Equal.whnf ty
  case tm of 
    -- c-lam: check the type of a function
    (Lam bnd) -> case ty' of
      (Pi tyA bnd2) -> Local.unbind bnd $ \(x,body) -> do
        -- unbind the variables in the lambda expression and pi type
        let tyB = Local.getBody bnd2
        -- check the type of the body of the lambda expression
        push x (checkType body tyB (Env.extendTy tyA ctx))
      _ -> Env.err [DS "Lambda expression should have a function type, not", DD ty']

    -- Practicalities
    (Pos p a) -> 
      Env.extendSourceLocation p a $ checkType a ty' ctx 

    TrustMe -> return ()

    PrintMe -> do
      Env.err [DS "Unmet obligation.\nContext:", DD ctx,
            DS "\nGoal:", DD ty']  

    -- c-let -- treat like immediate application
    (Let a bnd) ->  
      checkType (Local.instantiate bnd a) ty' ctx
      -- TODO: delay substitution and introduce new variable
      -- Local.unbind bnd $ \ (x, b) -> do
      -- tyA <- inferType a ctx
      -- push x (checkType (shift b) ty' (Env.extendTy tyA ctx))

    TmRefl -> case ty' of 
            (TyEq a b) -> Equal.equate a b
            _ -> Env.err [DS "Refl annotated with invalid type", DD ty']
    -- c-subst
    (Subst a b) -> do
      -- infer the type of the proof 'b'
      tp <- inferType b ctx
      -- make sure that it is an equality between m and n
      nf <- Equal.whnf tp
      (m, n) <- case nf of 
                  TyEq m n -> return (m,n)
                  _ -> Env.err [DS "Subst requires an equality type, not", DD tp]
      -- if either side is a variable, add a definition to the context
      -- if this fails, then the user should use contra instead
      edecl <- Equal.unify SZ m n
      -- if proof is a variable, add a definition to the context
      pdecl <- Equal.unify SZ b TmRefl
      -- I don't think this join can fail, but we have to check
      r' <- case joinR edecl pdecl of 
               Just r -> pure $ fromRefinement r
               Nothing -> Env.err [DS "incompatible equality in subst"]
      -- refine the result type
      let ty'' = applyE r' ty'
      -- refine the context
      let ctx' = case ctx of Env f -> Env $ \x -> applyE r' (f x)
      checkType a ty'' ctx'
      
    -- c-contra 
    (Contra p) -> do
      ty' <- inferType p ctx
      nf <- Equal.whnf ty'
      (a, b) <- case nf of 
                  TyEq m n -> return (m,n)
                  _ -> Env.err [DS "Contra requires an equality type, not", DD ty']
      a' <- Equal.whnf a
      b' <- Equal.whnf b
      case (a', b') of
        (DataCon da _, DataCon db _)
          | da /= db ->
            return ()
        (_, _) ->
          Env.err
            [ DS "I can't tell that",
              DD a',
              DS "and",
              DD b',
              DS "are contradictory"
            ]
            
    -- c-data
    -- we know the expected type of the data constructor
    -- so look up its type in the context
    (DataCon c args) -> do
      case ty' of
        (TyCon tname params) -> do
          ScopedConstructorDef delta (ConstructorDef cn theta) <- Env.lookupDCon c tname
          let numArgs = toInt $ Scoped.size theta
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
          case axiomPlusZ @n of 
            Refl -> do
              -- Env.warn [DS "calling substTele with params=", DL params]
              newTele <- 
                 withSNat (Scoped.size delta) $ substTele delta params theta
              Env.warn [DS "result is", DD newTele, DS "using to check args=", DL args]
              tcArgTele args newTele ctx
              
              return ()
        _ ->
          Env.err [DS "Unexpected type", DD ty', DS "for data constructor", DD tm]

    (Case scrut alts) -> do
      sty <- inferType scrut ctx
      (c, args) <- Equal.ensureTCon sty
      scrut' <- Equal.whnf scrut 
      let 
        checkAlt :: Match n -> TcMonad n ()
        checkAlt (Branch bnd) = Pat.unbind bnd $ \ (pat :: Pattern p) body -> do
            -- add variables from pattern to context
            (ctx', tm') <- declarePat pat (TyCon c args) ctx
            -- shift scrutinee and result type into the scope of the branch
            let scrut'' = applyE @Term (shiftNE (snat @p)) scrut'
            let ty1 = applyE @Term (shiftNE (snat @p)) ty'
            
            -- compare scrutinee and pattern: fails if branch is inaccessible
            defs <- push pat $ Equal.unify SZ scrut'' tm' 
            let r = fromRefinement defs
            -- refine body 
            let body' = applyE r body
            -- refine result type
            let ty'' = applyE r ty1
            ty3 <- push pat $ Equal.whnf ty''
            -- refine context
            let ctx'' = case ctx' of Env f -> Env $ \x -> applyE r (f x)
            -- check the branch
            push pat $ checkType body' ty'' ctx''
      mapM_ checkAlt alts
      exhaustivityCheck scrut' sty (map getSomePat alts) ctx
    
    -- c-infer
    _ -> do
      tyA <- inferType tm ctx
      Equal.equate tyA ty' 
    
getSomePat :: Match n -> Some Pattern
getSomePat (Branch bnd) = Some (Pat.getPat bnd)
---------------------------------------------------------------------
-- type checking datatype definitions, type constructor applications and 
-- data constructor applications
---------------------------------------------------------------------
-- Datatype definitions have two parts: 
--   Delta :: Telescope p1 Z 
--      a telescope of parameters to type constructor itself
--      top-level scope
--      cannot include definitions
--   Theta :: Telescope p2 p1 
--      a telescope of parameters to each data constructor
--      may include definitions, in the scope of Delta
-- Check Delta and each Theta when checking top-level datatype definition
-- Check Type constructor arguments against Delta
-- Instantiate Theta with type constructor arguments (could fail)
-- Check Data constructor arguments against Theta



-- | Check all of the types contained within a telescope
tcTypeTele :: forall p1 n. SNatI n =>
   Telescope p1 n -> Context n -> TcMonad n (Context (Plus p1 n))
tcTypeTele Tele ctx = return ctx
tcTypeTele (TCons (Scoped.Rebind (LocalDef x tm) (tl :: Telescope p2 n))) ctx = do
  ty1 <- inferType (Var x) ctx
  checkType tm ty1 ctx 
  Env.warn [DS "tcTypeTele: checking ", DD (Var x), DS "=", DD tm]
  -- TODO: substitute??!!! 
  case axiomPlusZ @p2 of
    Refl -> do
      tcTypeTele tl ctx
tcTypeTele (TCons (Scoped.Rebind (LocalDecl x ty) 
  (tl :: Telescope p2 (S n)))) ctx = do
  Env.warn [DS "tcTypeTele: checking ", DC x, DS ":", DD ty]
  tcType ty ctx
  case axiomAssoc @p2 @N1 @n of 
    Refl -> push x $ tcTypeTele tl (Env.extendTy ty ctx)

{-
G |- tm : A 
G |- tms : Theta {tm/x} ==> sigma
----------------------
G |- tm, tms : (x:A, Theta) ==> {tm/x},sigma 
-}

-- | type check a list of data constructor arguments against a telescope, returning a substitution
tcArgTele :: forall p n. SNatI n =>
  [Term n] -> Telescope p n -> Context n -> TcMonad n (Env Term p n)
tcArgTele [] Tele ctx = return zeroE
tcArgTele args (TCons (Scoped.Rebind (LocalDef x ty) (tele :: Telescope p2 n))) ctx = 
  case axiomPlusZ @p2 of 
    Refl -> do
       -- ensure that the equality is provable at this point
       Equal.equate (Var x) ty 
       tcArgTele args tele ctx
tcArgTele (tm : terms) (TCons (Scoped.Rebind (LocalDecl ln ty) 
          (tele :: Telescope p1 (S n)))) ctx = case axiomAssoc @p1 @N1 @n of 
    Refl -> do
      checkType tm ty ctx
      ss <- tcArgTele terms (applyE (tm .: idE) tele) ctx
      let t :: p :~: Plus p1 N1
          t = Refl
      return $ error "TODO: tcArgTele"

tcArgTele [] _ _ =
  Env.err [DS "Too few arguments provided."]
tcArgTele _ Tele _ =
  Env.err [DS "Too many arguments provided."]

-- | Make a substitution from a list of arguments. 
-- Checks that the length is as specified, and fails
-- otherwise
mkSubst :: forall p n.  
  [Term n] -> SNat p -> TcMonad n (Env Term (Plus p n) n)
mkSubst [] SZ = return idE
mkSubst (tm : tms) (SS m) = do
  ss <- mkSubst tms m
  return $ tm .: ss
mkSubst [] _ =
  Env.err [DS "Too few arguments provided."]
mkSubst _ SZ =
  Env.err [DS "Too many arguments provided."]



-- | increment all free variables by m
shiftNRE :: (SubstVar v) => SNat m -> Env v n (Plus n m)
shiftNRE m = Env (var . shiftRN m)

-- | Substitute a list of terms for the variables bound in a telescope
-- This is used to instantiate the parameters of a data constructor
-- to find the types of its arguments.
-- p1 : number of variables in delta
-- p2 : number of variables in thetai
-- This could fail if any constraints are not satisfiable.
-- TODO
substTele :: forall p1 p2 n. (SNatI n, SNatI p1) =>
             Telescope p1 Z    -- delta 
          -> [Term n]          -- params
          -> Telescope p2 p1   -- theta
          -> TcMonad n (Telescope p2 n)
substTele delta params theta = 
  do let delta' = applyE @Term (weakenE' (snat @n)) delta
     (ss :: Env Term (Plus p1 n) n) <- mkSubst (reverse params) (Scoped.size delta')
     let shift :: Env Term p1 (Plus p1 n)
         shift = Env (var . shiftRN (snat @n))
         weaken :: Env Term p1 (Plus p1 n)
         weaken = Env (var . weakenFinRight (snat @n))
     let theta' :: Telescope p2 (Plus p1 n)
         theta' = applyE @Term weaken theta
     doSubst @p1 ss theta'
  
{-
concatTele :: forall p1 p2 n. SNatI n =>
  Telescope p1 n -> Telescope p2 p1 -> Telescope (Plus p2 p1) n
concatTele Tele t2 = 
   case (axiomPlusZ @p2, axiomPlusZ @n) of 
      { (Refl, Refl) -> applyE @Term (weakenE' (snat @n)) t2 }
concatTele (TCons (Scoped.Rebind (l :: Local p n) t1)) t2 = 
  withSNat (sPlus (Scoped.size l) (snat @n)) $ 
    let t2' = concatTele t1 t2 in
    TCons (Scoped.Rebind l t2')
-}
-- Propagate the given substitution through a telescope, potentially
-- reworking the constraints

doSubst :: forall q n p. SNatI n => Env Term (Plus q n) n -> Telescope p (Plus q n) -> TcMonad n (Telescope p n)
doSubst r Tele = return Tele
doSubst r (TCons (Scoped.Rebind e (t :: Telescope p2 m))) = case e of 
    LocalDef x (tm :: Term (Plus q n)) -> case (axiomPlusZ @q, axiomPlusZ @p2) of 
      (Refl,Refl) -> do
        let tx' = applyE r (Var x)
        let tm' = applyE r tm
        defs <- Equal.unify SZ tx' tm'
        (tele' :: Telescope p2 n) <- doSubst @q r t 
        return $ appendDefs defs tele'

    LocalDecl nm (ty :: Term (Plus q n)) -> do
      let fact :: Plus q (S n) :~: S (Plus q n)
          fact = axiomM @N1 @q @n
      case fact of 
        Refl -> do
          let ty' = applyE r ty
          (t' :: Telescope p2 (S n)) <- push nm $ doSubst @q @(S n) (up r) t
          return $ TCons (Scoped.Rebind (LocalDecl nm ty') t')

appendDefs :: Refinement Term n -> Telescope p n -> Telescope p n
appendDefs (Refinement m) = go (Map.toList m) where
   go :: forall n p. [(Fin n, Term n)] -> Telescope p n -> Telescope p n
   go [] t = t
   go ((x,tm):defs) (t :: Telescope p1 n) = 
    case axiomPlusZ @p1 of 
      Refl -> TCons (Scoped.Rebind (LocalDef x tm) (go defs t))

-----------------------------------------------------------
-- Typechecking pattern matching
-----------------------------------------------------------

-- | Create a binding for each of the variables in the pattern, producing an extended context and 
-- a term corresponding to the variables
declarePat :: forall p n. SNatI n =>
  Pattern p -> Typ n -> Context n -> TcMonad n (Context (Plus p n), Term (Plus p n))
declarePat (PatVar x) ty ctx = do
  pure (Env.extendTy ty ctx, Var f0)
declarePat (PatCon dc (pats :: PatList p)) ty ctx = do 
  (tc,params) <- Equal.ensureTCon ty 
  ScopedConstructorDef (delta :: Telescope p1 'Z) 
      (ConstructorDef cn (thetai :: Telescope p2 p1)) <- Env.lookupDCon dc tc
  case axiomPlusZ @n of 
    Refl ->
      case testEquality (Pat.size pats) (Scoped.size thetai) of
         Just Refl -> do
           (tele :: Telescope p2 n) <- 
               withSNat (Scoped.size delta) $ substTele delta params thetai
           (ctx', tms') <- declarePats pats tele ctx
           pure (ctx', DataCon dc tms')
         Nothing -> Env.err [DS "Wrong number of arguments to data constructor", DC cn]

-- | Given a list of pattern arguments and a telescope, create a binding for 
-- each of the variables in the pattern
-- pt should be the length of the pattern list, not the number of variables bound in it 
declarePats :: forall p pt n. SNatI n =>
  PatList p -> Telescope pt n -> Context n -> TcMonad n (Context (Plus p n), [Term (Plus p n)])
declarePats pats (TCons (Scoped.Rebind (LocalDef x ty) (tele :: Telescope p1 n))) ctx = do
  case axiomPlusZ @p1 of 
    Refl -> do
      (ctx', tms')  <- declarePats pats tele ctx
      -- TODO: substitute for x in tele'
      pure (ctx', tms')
declarePats (PCons (p1 :: Pattern p1) (p2 :: PatList p2)) 
  (TCons (Scoped.Rebind (LocalDecl x ty1) (tele2 :: Telescope p3 (S n)))) ctx = do
    let fact :: Plus p2 (Plus p1 n) :~: Plus p n
        fact = axiomAssoc @p2 @p1 @n
    case fact of
      Refl -> do
        (ctx1 :: Context (Plus p1 n), tm :: Term (Plus p1 n)) <- declarePat @p1 p1 ty1 ctx
        let ss :: Env Term (S n) (Plus p1 n)
            ss = instantiateWeakenEnv (Pat.size p1) (snat @n) tm
        let tele' :: Telescope p3 (Plus p1 n)
            tele' = applyE ss tele2
        (ctx2  :: Context (Plus p2 (Plus p1 n)), 
           tms  :: [Term (Plus p2 (Plus p1 n))]) <- 
              withSNat (sPlus (Pat.size p1) (snat @n)) $ 
              push p1 $
                 declarePats @p2 @p3 @(Plus p1 n) p2 tele' ctx1
        return (ctx2, applyE @Term (shiftNE (Pat.size p2)) tm : tms)
declarePats PNil Tele ctx = return (ctx, [])
declarePats PNil _ _ = Env.err [DS "Not enough patterns in match for data constructor"]
declarePats pats Tele ctx = Env.err [DS "Too many patterns in match for data constructor"]

-- Add to Scoped
instantiateWeakenEnv ::
  forall p n v c.
  (SubstVar v, Subst v v) =>
  SNat p ->
  SNat n ->
  v (Plus p n) ->
  Env v (S n) (Plus p n)
instantiateWeakenEnv p n a = 
  shiftNE @v p
    .>> Env
      ( \(x :: Fin (Plus p (S n))) ->
          case checkBound @p @(S n) p x of
            Left pf -> var (weakenFinRight n pf)
            Right pf -> case pf of
              FZ -> a
              FS (f :: Fin n) -> var (shiftN p f)
      )

-- | Convert a pattern to a term 
{-
pat2Term :: Pattern ->  Term
pat2Term (PatVar x) = Var x
pat2Term (PatCon dc pats) = DataCon dc (pats2Terms pats) 
  where
    pats2Terms :: [(Pattern, Epsilon)] -> [Arg]
    pats2Terms [] = []
    pats2Terms ((p, ep) : ps) = Arg ep t : ts where
      t = pat2Term p 
      ts = pats2Terms ps
-}       





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
      liftIO $ putStrLn $ "Checking module " ++ show name
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
  do term' <- Env.lookupGlobalDef n
     Env.extendSourceLocation (unPosFlaky term) term 
        (Env.err
          [ DS "Multiple definitions of",
            DC n,
            DS "Previous definition was",
            DD term'
          ]) 
  `catchError` \_ -> do
      traceM $ "****checking def****" 
      traceM $ n ++ " = " ++ pp term
      lkup <- Env.lookupHint n
      case lkup of
        Nothing -> do
          ty <- inferType term Env.emptyContext
          return $ AddCtx [ModuleDecl n ty, ModuleDef n term]
        Just ty -> do
          let decl = ModuleDecl n ty
          Env.extendCtx decl $ checkType term ty Env.emptyContext 
          return (AddCtx [decl, ModuleDef n term])
             `Env.extendErr` 
                [ 
                    DS "When checking the term",
                    DD term,
                    DS "against the type",
                    DC decl
                  ]
                 

tcEntry decl@(ModuleDecl x ty) = do
  traceM $ "****checking decl****" 
  traceM $ pp decl
  duplicateTypeBindingCheck decl
  tcType ty Env.emptyContext
  return (AddHint x ty)
    `Env.extendErr` [ 
                    DS "when checking the type declaration",
                    DS x, DS ":", DC ty
                  ]
-- rule Entry_data
tcEntry decl@(ModuleData n (DataDef (delta :: Telescope n Z) s cs)) = do
  traceM $ "****checking datadef****" 
  traceM $ pp decl
  case axiomPlusZ @n of 
    Refl -> do
        -- Check that the telescope for the datatype definition is well-formed
      ctx' <- tcTypeTele delta Env.emptyContext
      ---- check that the telescope provided
      ---  for each data constructor is wellfomed, and elaborate them
      let checkConstructorDef defn@(ConstructorDef d theta) = case axiomPlusZ @n of 
            Refl -> withSNat (Scoped.size delta) $ do
            -- TODO: add source position
            -- Env.extendSourceLocation pos defn $
              push delta $ do
                s <- scope
                Env.warn (DS "in scope" : map DC (toList (scope_locals s)))
                Env.warn [DS "checking constructor", DC d, DD theta]
                tcTypeTele theta ctx'
              return ()
                `Env.extendErr`[ DS "when checking the constructor declaration",
                                 DC defn ]
      Env.extendCtx (ModuleData n (DataDef delta s [])) 
                $ mapM_ checkConstructorDef cs
      -- Implicitly, we expect the constructors to actually be different...
      let cnames = map (\(ConstructorDef c _) -> c) cs
      unless (length cnames == length (nub cnames)) $
        Env.err [DS "Datatype definition", DC n, 
                 DS "contains duplicated constructors"]
      return (AddCtx [decl])
        `Env.extendErr` [ 
                    DS "when checking the datatype declaration",
                    DC decl
                  ]

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
              DC decl,
              DS "Previous was",
              DD decl'
            ]
       in Env.extendSourceLocation p decl $ Env.err msg

-----------------------------------------------------------
-- Checking that pattern matching is exhaustive
-----------------------------------------------------------
data Some (p :: Nat -> Type) where Some :: forall x p. SNatI x => (p x) -> Some p 

-- | Given a particular type and a list of patterns, make
-- sure that the patterns cover all potential cases for that
-- type.
-- If the list of patterns starts with a variable, then it doesn't
-- matter what the type is, the variable is exhaustive. (This code
-- does not report unreachable patterns.)
-- Otherwise, the scrutinee type must be a type constructor, so the
-- code looks up the data constructors for that type and makes sure that
-- there are patterns for each one.

exhaustivityCheck :: forall n. (SNatI n) => Term n -> Typ n -> [Some Pattern] -> Context n -> TcMonad n ()
exhaustivityCheck _scrut ty (Some (PatVar x) : _) ctx = return ()
exhaustivityCheck _scrut ty pats ctx = do
  (tcon, tys) <- Equal.ensureTCon ty
  DataDef (delta :: Telescope p1 Z) sort datacons <- Env.lookupTCon tcon
  let   loop :: [Some Pattern] -> [ConstructorDef p1] -> TcMonad n ()
        loop  [] [] = return ()
        loop  [] dcons = do
          l <- checkImpossible dcons
          if null l
            then return ()
            else Env.err $ DS "Missing case for" : map DC l
        loop  (Some (PatVar x) : _) dcons = return ()
        loop  (Some (PatCon dc (args :: PatList p)) : pats') dcons = do
          (ConstructorDef _ (tele :: Telescope p2 p1), dcons') <- removeDCon dc dcons
          case testEquality (snat @p) (Scoped.size tele) of 
            Just Refl -> do
                tele' <- 
                  withSNat (Scoped.size delta) $ substTele delta tys tele
                let (aargs, pats'') = relatedPats dc pats'
                -- check the arguments of the data constructor together with 
                -- all other related argument lists
                checkSubPats dc tele' (Some args : aargs)
                loop pats'' dcons'
            Nothing -> error "BUG: removeDCon returned invalid constructor"

        -- make sure that the given list of constructors is impossible
        -- in the current environment
        checkImpossible :: [ConstructorDef p1] -> TcMonad n [DataConName]
        checkImpossible [] = return []
        checkImpossible (ConstructorDef dc tele : rest) = do
          this <-
            ( do
                tele' <- withSNat (Scoped.size delta) $ 
                   substTele delta tys tele
                tcTypeTele tele' ctx
                return [dc]
              )
              `catchError` (\_ -> return [])
          others <- checkImpossible rest
          return (this ++ others)
  loop pats datacons
    


-- | Given a particular data constructor name and a list of data
-- constructor definitions, pull the definition out of the list and
-- return it paired with the remainder of the list.
removeDCon :: DataConName -> [ConstructorDef p1] ->
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
relatedPats :: DataConName -> [Some Pattern] -> ([Some PatList], [Some Pattern])
relatedPats dc [] = ([], [])
relatedPats dc (pc@(Some (PatVar _)) : pats) = ([], pc : pats)
relatedPats dc (pc@(Some (PatCon dc' args)) : pats)
  | dc == dc' =
    let (aargs, rest) = relatedPats dc pats
     in (Some args : aargs, rest)
relatedPats dc (pc : pats) =
  let (aargs, rest) = relatedPats dc pats
   in (aargs, pc : rest)


-- | Occurs check for the subpatterns of a data constructor. Given
-- the telescope specifying the types of the arguments, plus the
-- subpatterns identified by relatedPats, check that they are each
-- exhaustive. (This is the PatList version of `exhaustivityCheck`)

-- for simplicity, this function requires that all subpatterns
-- are pattern variables.
checkSubPats :: forall p n. DataConName -> Telescope p n -> [Some PatList] -> TcMonad n ()
checkSubPats dc Tele _ = return ()
checkSubPats dc (TCons (Scoped.Rebind (LocalDef _ _) (tele :: Telescope p2 n))) (patss :: [Some PatList]) = 
  checkSubPats dc tele patss
checkSubPats dc (TCons (Scoped.Rebind (LocalDecl x _) (tele :: Telescope p2 (S n)))) 
                (patss :: [Some PatList]) = do
      case allHeadVars patss of 
        Just tls -> push x $ checkSubPats @_ @(S n) dc tele tls
        Nothing -> Env.err [DS "All subpatterns must be variables in this version."]


nullPatList :: PatList p -> Bool
nullPatList PNil = True
nullPatList _ = False

allHeadVars :: [Some PatList] -> Maybe [Some PatList]
allHeadVars [] = Just []
allHeadVars (Some (PCons (PatVar x) (pats :: PatList p2)) : patss) = do
  withSNat (Pat.size pats) $
    (Some pats :) <$> allHeadVars patss
allHeadVars _ = Nothing