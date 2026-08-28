{-# OPTIONS --erasure #-}

-- |
-- Module      : Test
-- Description : Runtime tests for the three talk transcriptions
--
-- The evaluators in Talk1, Talk2 and Talk3 really are partial -- they
-- diverge on @(λx. x x) (λx. x x)@ -- and are marked NON_TERMINATING.
-- Agda therefore refuses to unfold them while type checking, which keeps
-- type checking decidable but also means their results cannot be checked
-- by a @Refl@ proof.  They have to be /run/.
--
-- So this is an ordinary program.  Compile and run it:
--
-- @
-- agda --compile --compile-dir=build talks/Test.agda
-- ./build/Test
-- @
--
-- That is the same bargain Haskell makes everywhere: general recursion
-- is allowed, and correctness of a partial function is established by
-- testing rather than by the type checker.
module Test where

open import Agda.Builtin.IO   using (IO)
open import Agda.Builtin.Unit   using (⊤)
open import Agda.Builtin.String using (primStringAppend)

open import Data.Prelude using (String; Bool; true; false; _&&_; not;
                                Maybe; Just; Nothing)

import Talk1
import Talk2
import Talk3
import DepMatch
import SystemF
import LC
import ScopeCheck
import LCLet
import PTS
import Pat
import PatGen
import LCWF
import LinLC
import TaggedSystemF
import PureSystemF

------------------------------------------------------------------------
-- * A tiny test harness
------------------------------------------------------------------------

postulate
  putStrLn : String → IO ⊤
  _then_   : {A B : Set} → IO A → IO B → IO B
  done     : IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as T #-}
{-# COMPILE GHC putStrLn = T.putStrLn      #-}
{-# COMPILE GHC _then_   = \ _ _ -> (>>)   #-}
{-# COMPILE GHC done     = return ()       #-}

infixr 1 _then_

check : String → Bool → IO ⊤
check name true  = putStrLn (primStringAppend "pass  " name)
check name false = putStrLn (primStringAppend "FAIL  " name)

------------------------------------------------------------------------
-- * Part I: environments as functions
------------------------------------------------------------------------

module T1 where
  open Talk1

  eqTm : ∀ {@0 n} → Tm n → Tm n → Bool
  eqTm (Var x)   (Var y)   = eqFin x y
  eqTm (Lam a)   (Lam b)   = eqTm a b
  eqTm (App a b) (App c d) = eqTm a c && eqTm b d
  eqTm _         _         = false

  eqVal : Val → Val → Bool
  eqVal (VLam a) (VLam b) = eqTm a b

  -- (λx.x) (λx.x)  ⟶  λx.x
  test-eval : Bool
  test-eval = eqVal (eval (App ex-id ex-id)) (VLam (Var FZ))

  -- substituting under a binder shifts the substituted term:
  --   [λx.x / y] (λz. y)  =  λz. λx. x
  test-subst : Bool
  test-subst = eqTm (applyE (ex-id ∷ idE) (Lam (Var (FS FZ))))
                    (Lam (Lam (Var FZ)))

------------------------------------------------------------------------
-- * Part II: environments as shift lists
------------------------------------------------------------------------

module T2 where
  open Talk2
  open import Data.Nat
  open import Data.Fin using (Fin; FZ; FS; eqFin)

  ex-id : Tm Z
  ex-id = Lam (Var FZ)

  eqTm : ∀ {@0 n} → Tm n → Tm n → Bool
  eqTm (Var x)   (Var y)   = eqFin x y
  eqTm (Lam a)   (Lam b)   = eqTm a b
  eqTm (App a b) (App c d) = eqTm a c && eqTm b d
  eqTm _         _         = false

  eqVal : Val → Val → Bool
  eqVal (VLam a) (VLam b) = eqTm a b

  test-eval : Bool
  test-eval = eqVal (eval (App ex-id ex-id)) (VLam (Var FZ))

  test-subst : Bool
  test-subst = eqTm (applyE (ex-id ∷ idE) (Lam (Var (FS FZ))))
                    (Lam (Lam (Var FZ)))

  -- The point of the representation: two delayed shifts are fused into a
  -- single traversal when the variable is finally looked up.
  test-fuse : Bool
  test-fuse = eqTm ((Shift 2 (Shift 3 idE)) ! (FZ {2}))
                   (Var (FS (FS (FS (FS (FS FZ))))))

  -- `shiftE` is a smart constructor: shifting an environment that is
  -- already a shift produces one node, not two.
  isOneShift : ∀ {@0 m n} → Env m n → Bool
  isOneShift (Shift _ Id) = true
  isOneShift _            = false

  test-smart : Bool
  test-smart = isOneShift (shiftE (Shift 3 (idE {0})))

------------------------------------------------------------------------
-- * Part III: the rebound library, with pattern binders
------------------------------------------------------------------------

module T3 where
  open Talk3
  open import Rebound
  open import Rebound.Bind.Pat using (bind)

  eqMaybeTm : Maybe (Tm Z) → Maybe (Tm Z) → Bool
  eqMaybeTm (Just a) (Just b) = eqTm a b
  eqMaybeTm Nothing  Nothing  = true
  eqMaybeTm _        _        = false

  -- case inj1 ((), ()) of { inj1 (x, y) → y }
  test-match : Bool
  test-match = eqMaybeTm (eval ex) (Just Unit)

  -- case ((), inj0 ()) of { (x, y) → y }
  ex2 : Tm Z
  ex2 = Match (Pair Unit (Inj 0 Unit))
              (BCons (bind (PPair PVar PVar) (Var f0)) BNil)

  test-select : Bool
  test-select = eqMaybeTm (eval ex2) (Just (Inj 0 Unit))

  -- The library environment distinguishes raising the bound from
  -- shifting the variables: `Weak 2` leaves index 1 alone, `Inc 2` moves
  -- it to index 3.
  test-weak : Bool
  test-weak = eqTm (applyEnv {Tm} (Weak 2) (f1 {0})) (Var (f1 {2}))

  test-inc : Bool
  test-inc = eqTm (applyEnv {Tm} (Inc 2) (f1 {0})) (Var (f3 {0}))

  -- `comp` really does fuse, rather than building a suspended `_:<>_`.
  isInc : ∀ {a : @0 Nat → Set} {@0 m n} → Env a m n → Bool
  isInc (Inc _) = true
  isInc _       = false

  test-fuse : Bool
  test-fuse = isInc (Inc {Tm} {2} 1 >>> Inc 2)

  test-cancel : Bool
  test-cancel = isInc (Inc {Tm} {2} 1 >>> (Unit ∷ Inc 0))

------------------------------------------------------------------------
-- * DepMatch: dependent pattern matching with scoped patterns
------------------------------------------------------------------------

module T4 where
  open DepMatch using (Exp; Pat; Result; ok; err; pat0; tm0; tmid; tyid;
                       tmEx; tyEx; t0; t1; patternMatch; checkType;
                       eval; App; Match)
  open import Rebound.Context using (emptyC)

  isOk : {A : Set} → Result A → Bool
  isOk (ok _)  = true
  isOk (err _) = false

  isJust : {A : Set} → Maybe A → Bool
  isJust (Just _) = true
  isJust Nothing  = false

  -- the telescopic pattern (x, (y : x)) matches the pair (*, Sigma x:*.x)
  test-telescope : Bool
  test-telescope = isJust (patternMatch pat0 tm0)

  -- the polymorphic identity really does have the polymorphic identity type
  test-tmid : Bool
  test-tmid = isOk (checkType emptyC tmid tyid)

  -- a nested dependent pattern match type-checks
  test-tmEx : Bool
  test-tmEx = isOk (checkType emptyC tmEx tyEx)

  -- ... and the checker is not vacuous: this one must be rejected
  test-reject : Bool
  test-reject = not (isOk (checkType emptyC tmid tyEx))

  -- evaluation still reduces
  test-eval : Bool
  test-eval = isMatch (eval (App t1 t0))
    where
      isMatch : ∀ {@0 n} → Exp n → Bool
      isMatch (Match _) = true
      isMatch _         = false

------------------------------------------------------------------------
-- * Ported examples
------------------------------------------------------------------------

module T5 where
  open LC using (Exp; eqExp; nf; nfEnv; eval; t; t0; t2; lam; v0; Lam; App; Var)
  open import Rebound.Lib using (Z)

  -- the two normalizers agree on a term with a redex under a binder
  test-nf : Bool
  test-nf = eqExp (nf t2) (nfEnv t2)

  -- (λx.λy.x) ((λz.z) (λz.z))  reduces to  λy. λz. z
  test-eval : Bool
  test-eval = eqExp (eval t2) (lam (lam v0))

module T6 where
  open ScopeCheck using (scopeCheck; eqName; idExp; illScoped)

  isJust : {A : Set} → Maybe A → Bool
  isJust (Just _) = true
  isJust Nothing  = false

  test-scoped : Bool
  test-scoped = isJust (scopeCheck eqName idExp)

  test-illscoped : Bool
  test-illscoped = not (isJust (scopeCheck eqName illScoped))

module T7 where
  open SystemF using (Ty; Exp; TVar; TAll; TArr; EVar; ELam; EApp; ETLam; ETApp;
                      FCtx; Empty; ConsTmVar; ConsTyVar; tc; eqTy; mkTyExp)
  open import Rebound.Bind.Single using (bind)
  open import Rebound.Lib using (Z; S; f0)

  isJust : {A : Set} → Maybe A → Bool
  isJust (Just _) = true
  isJust Nothing  = false

  -- ΛA. λx:A. x   should have type   ∀A. A → A
  polyId : Exp Z Z
  polyId = ETLam (bind (mkTyExp (ELam (TVar f0) (bind (EVar f0)))))

  test-tc : Bool
  test-tc = isJust (tc Empty polyId)

module T8 where
  open LCLet using (Exp; eval; t2; t3; t4; Lam)

  isLam : ∀ {@0 n} → Exp n → Bool
  isLam (Lam _) = true
  isLam _       = false

  -- let I in (0 0)   evaluates to   I
  test-let : Bool
  test-let = isLam (eval t2)

  -- a telescope of lets evaluates without getting stuck
  test-tele : Bool
  test-tele = isLam (eval t4)

module T9 where
  open PTS using (Exp; Result; ok; err; tyid; tmid; t0; t1; checkType; nf;
                  Star; Pi; Lam; Var; App; Sigma; Pair; Split)
  open import Rebound.Context using (emptyC)

  isOk : {A : Set} → Result A → Bool
  isOk (ok _)  = true
  isOk (err _) = false

  -- λA:*. λx:A. x   has type   ΠA:*. A → A
  test-tmid : Bool
  test-tmid = isOk (checkType emptyC tmid tyid)

  -- ... and does not have type *
  test-reject : Bool
  test-reject = not (isOk (checkType emptyC tmid Star))

module T10 where
  open Pat using (Exp; eval; t2; t3; t4; Con; App; Var; patEqPat; pp1; pp2;
                  patternMatch; e1; e2)
  open import Rebound.Lib using (Z; S; f0)

  isJust : {A : Set} → {B : Set} → Maybe B → Bool
  isJust (Just _) = true
  isJust Nothing  = false

  isCon : ∀ {@0 n} → Exp n → Bool
  isCon (Con _) = true
  isCon _       = false

  -- t4's scrutinee is built from "cons" but its pattern says "Cons", so
  -- no branch matches and evaluation is stuck on the Case.
  test-stuck : Bool
  test-stuck = not (isCon (eval t4))

  -- with a scrutinee that really does match, the branch is selected and
  -- its body (the second bound variable) is returned
  t5 : Exp Z
  t5 = App t2 (App (App (Con "Cons") (Con "a")) (Con "nil"))

  test-case : Bool
  test-case = isCon (eval t5)

  -- a constructor pattern matches its own constructor, not another's
  test-match : Bool
  test-match = isJust {Exp Z} (patternMatch pp1 e1)
             && not (isJust {Exp Z} (patternMatch pp1 e2))

module T11 where
  open PatGen using (Exp; appearsFreeExp; t0; t3; Var; Con; App)
  open import Rebound.Lib using (f0; Z; S)

  -- `Con "a"` has no free variables; `Var f0` has one
  test-fv : Bool
  test-fv = not (appearsFreeExp f0 (Con {S Z} "a"))
          && appearsFreeExp f0 (Var {S Z} f0)

module T12 where
  open LCWF using (Exp; Env; Id; Cons; Var; App; Lam; applyE; size; idExp)
  open import Rebound.Lib using (Z; S; FZ; FS; eqNat)

  -- LCWF's `applyE` is *proved* terminating, so the real assertions are
  -- the `Refl` proofs inside the module itself -- checked when the file
  -- is type-checked, not here.  This just confirms it also runs.
  test-runs : Bool
  test-runs = eqNat (size (applyE (Cons idExp (Id {Z})) (App (Var FZ) (Var FZ))))
                    (size (App idExp idExp))

module T13 where
  open LinLC using (Ty; TyUnit; _~>_; Exp; idExp; dropExp; runTC; checkType)
  open import Data.Vec using (VNil)
  open import Data.Prelude using (Either; Left; Right)

  isRight : {E A : Set} → Either E A → Bool
  isRight (Right _) = true
  isRight (Left _)  = false

  -- λx. x  is linear at  Unit ⊸ Unit
  test-linear : Bool
  test-linear = isRight (runTC VNil (checkType idExp (TyUnit ~> TyUnit)))

  -- λx. λy. x  drops y, so the linear checker must reject it
  test-nonlinear : Bool
  test-nonlinear =
    not (isRight (runTC VNil (checkType dropExp (TyUnit ~> (TyUnit ~> TyUnit)))))

module T14 where
  open TaggedSystemF using (Ty; Tm; inferType; runTC; emptyEnv; eqExp;
                            polyId; polyIdTy; bad)
  open import Data.Prelude using (Either; Left; Right)

  -- ΛA. λx:A. x   infers   ∀A. A → A
  test-polyid : Bool
  test-polyid = chk (runTC emptyEnv (inferType polyId))
    where
      chk : Either String (Ty _) → Bool
      chk (Right t) = eqExp t polyIdTy
      chk (Left _)  = false

  -- ΛA. λx:A. x x   must be rejected
  test-bad : Bool
  test-bad = chk (runTC emptyEnv (inferType bad))
    where
      chk : Either String (Ty _) → Bool
      chk (Right _) = false
      chk (Left _)  = true

module T15 where
  open PureSystemF using (Exp; inferType; runTC; emptyEnv; eqExp; pp;
                          t0; t1; t2)
  open import Data.Prelude using (Either; Left; Right; eqString)
  open import Data.Vec using (VNil)

  isRight : {E A : Set} → Either E A → Bool
  isRight (Right _) = true
  isRight (Left _)  = false

  -- ΛX. λx:X. x  and the larger polymorphic term both type-check
  test-tc : Bool
  test-tc = isRight (runTC emptyEnv (inferType t0))
         && isRight (runTC emptyEnv (inferType t1))

  -- t2 abstracts a *term* variable over a Kind and then returns a type
  -- mentioning it — a dependent function type, which System F has not.
  -- Strengthening the result type fails, and the checker says so.
  test-t2-rejected : Bool
  test-t2-rejected = not (isRight (runTC emptyEnv (inferType t2)))

  -- the scope-indexed reader carries names under binders correctly
  test-pp : Bool
  test-pp = eqString (pp VNil t0) "ΛX. λx. x"

------------------------------------------------------------------------
-- * Main
------------------------------------------------------------------------

main : IO ⊤
main =
  putStrLn "Part I  -- environments as functions"           then
  check "eval (λx.x) (λx.x)          " T1.test-eval         then
  check "substitution under a binder  " T1.test-subst       then
  putStrLn "Part II -- environments as shift lists"         then
  check "eval (λx.x) (λx.x)          " T2.test-eval         then
  check "substitution under a binder  " T2.test-subst       then
  check "delayed shifts fuse on lookup" T2.test-fuse        then
  check "shiftE fuses adjacent shifts  " T2.test-smart       then
  putStrLn "Part III -- the rebound library"                then
  check "pattern match selects branch " T3.test-match       then
  check "pair pattern binds both vars " T3.test-select      then
  check "Weak raises the bound only   " T3.test-weak        then
  check "Inc shifts the variable      " T3.test-inc         then
  check "comp fuses Inc with Inc      " T3.test-fuse        then
  check "comp cancels Inc against Cons" T3.test-cancel      then
  putStrLn "DepMatch -- scoped patterns, dependent matching"      then
  check "telescopic pattern matches   " T4.test-telescope   then
  check "polymorphic id checks        " T4.test-tmid        then
  check "nested dependent match checks" T4.test-tmEx        then
  check "ill-typed term is rejected   " T4.test-reject      then
  check "evaluation reduces           " T4.test-eval        then
  putStrLn "Examples -- LC, ScopeCheck, SystemF"            then
  check "nf and nfEnv agree           " T5.test-nf          then
  check "cbn eval reduces to identity " T5.test-eval        then
  check "scope check accepts closed   " T6.test-scoped      then
  check "scope check rejects open     " T6.test-illscoped   then
  check "System F infers poly identity" T7.test-tc          then
  check "let-binding evaluates        " T8.test-let         then
  check "let-telescope evaluates      " T8.test-tele        then
  check "PTS checks polymorphic id    " T9.test-tmid        then
  check "PTS rejects ill-typed term   " T9.test-reject      then
  check "constructor pattern matching " T10.test-match      then
  check "case selects and reduces     " T10.test-case       then
  check "unmatched case gets stuck    " T10.test-stuck      then
  check "free-variable test           " T11.test-fv         then
  check "proved-terminating subst runs" T12.test-runs       then
  check "linear term type-checks     " T13.test-linear     then
  check "non-linear term rejected    " T13.test-nonlinear  then
  check "tagged SysF infers ∀A. A → A " T14.test-polyid     then
  check "tagged SysF rejects x x      " T14.test-bad        then
  check "pure SysF type-checks        " T15.test-tc         then
  check "pure SysF rejects dependent  " T15.test-t2-rejected then
  check "pretty printer names binders " T15.test-pp         then
  done
