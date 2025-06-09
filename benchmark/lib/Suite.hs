-- Various collections of implementations
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use :" #-}
module Suite where

import qualified Rebound.Env.Strict.Env
import qualified Rebound.Env.Strict.EnvGen
import qualified Rebound.Env.Strict.Bind
import qualified Rebound.Env.Strict.Subst
import qualified Rebound.Env.Strict.EnvV
import qualified Rebound.Env.Strict.EnvGenV
import qualified Rebound.Env.Strict.BindV
import qualified Rebound.Env.Lazy.EvalV
import qualified Rebound.Env.Lazy.Env
import qualified Rebound.Env.Lazy.EnvV
import qualified Rebound.Env.Lazy.EnvGenV
import qualified Rebound.Env.Lazy.Bind
import qualified Rebound.Env.Lazy.BindV
import qualified Rebound.Env.Lazy.Subst
import qualified Rebound.Env.Lazy.SubstV
import qualified Rebound.Env.Lazy.ExpSubstV
import qualified Rebound.Env.Lazy.ExpSubstEnvV
import qualified Rebound.Manual.Strict.Env
import qualified Rebound.Manual.Strict.Bind
import qualified Rebound.Manual.Strict.BindV
import qualified Rebound.Manual.Strict.Subst
import qualified Rebound.Manual.Strict.SubstV
import qualified Rebound.Manual.Strict.EvalV
import qualified Rebound.Manual.Lazy.Env
import qualified Rebound.Manual.Lazy.EnvV
import qualified Rebound.Manual.Lazy.EnvVal
import qualified Rebound.Manual.Lazy.Bind
import qualified Rebound.Manual.Lazy.BindV
import qualified Rebound.Manual.Lazy.Subst
import qualified Rebound.Manual.Lazy.SubstV
import qualified Rebound.Manual.Lazy.Eval
import qualified Rebound.Manual.Lazy.EvalV
import qualified Rebound.Manual.Lazy.EnvOnlyV
import qualified Rebound.Manual.Lazy.ExpSubstV
import qualified Rebound.Manual.Lazy.ExpSubstEnvV
import qualified Core.Nf
import qualified DeBruijn.Bound
import qualified DeBruijn.BoundV
import qualified DeBruijn.CPDT
import qualified DeBruijn.Cornell
import qualified DeBruijn.Kit
import qualified DeBruijn.Krivine
import qualified DeBruijn.KrivineScoped
import qualified DeBruijn.Lazy.Bound
import qualified DeBruijn.Lazy.CPDT
import qualified DeBruijn.Lazy.Cornell
import qualified DeBruijn.Lazy.Kit
import qualified DeBruijn.Lazy.Lennart
import qualified DeBruijn.Lazy.Lift
import qualified DeBruijn.Lazy.Nested
import qualified DeBruijn.Lazy.Par.B
import qualified DeBruijn.Lazy.Par.Fun
import qualified DeBruijn.Lazy.Par.GB
import qualified DeBruijn.Lazy.Par.L
import qualified DeBruijn.Lazy.Par.P
import qualified DeBruijn.Lazy.Par.Scoped
import qualified DeBruijn.Lazy.TAPL
import qualified DeBruijn.Lennart
import qualified DeBruijn.Lift
import qualified DeBruijn.Nested
import qualified DeBruijn.NestedV
import qualified DeBruijn.Par.B
import qualified DeBruijn.Par.Fun
import qualified DeBruijn.Par.GB
import qualified DeBruijn.Par.L
import qualified DeBruijn.Par.P
import qualified DeBruijn.Par.Scoped
import qualified DeBruijn.TAPL
import qualified Lennart.DeBruijn
import qualified Lennart.HOAS
import qualified Lennart.Simple
import qualified Lennart.SimpleOrig
import qualified Lennart.Unique
import qualified LocallyNameless.GenericInstOpt
import qualified LocallyNameless.GenericOpt
import qualified LocallyNameless.Lazy.GenericInstOpt
import qualified LocallyNameless.Lazy.GenericOpt
import qualified LocallyNameless.Lazy.Opt
import qualified LocallyNameless.Lazy.Ott
import qualified LocallyNameless.Lazy.ParOpt
import qualified LocallyNameless.Lazy.ParScoped
import qualified LocallyNameless.Lazy.SupportOpt
import qualified LocallyNameless.Lazy.TypedOtt
import qualified LocallyNameless.Opt
import qualified LocallyNameless.Ott
import qualified LocallyNameless.ParOpt
import qualified LocallyNameless.ParScoped
import qualified LocallyNameless.SupportInstOpt
import qualified LocallyNameless.SupportOpt
import qualified LocallyNameless.TypedOpt
import qualified LocallyNameless.TypedOtt
import qualified NBE.Aelig
import qualified NBE.Boesflug
import qualified NBE.Contextual
import qualified NBE.Felgenhauer
import qualified NBE.Kovacs
import qualified NBE.KovacsNamed
import qualified NBE.Lazy.KovacsScoped
import qualified NBE.KovacsScoped
import qualified NBE.KovacsScoped2
import qualified Named.Lazy.Foil
import qualified Named.Lazy.NominalG
import qualified Named.Lazy.Simple
import qualified Named.Lazy.SimpleGH
import qualified Named.Lazy.SimpleH
import qualified Named.Lazy.SimpleM
import qualified Named.Foil
import qualified Named.FoilV
import qualified Named.Lennart
import qualified Named.NominalG
import qualified Named.Simple
import qualified Named.SimpleGH
import qualified Named.SimpleH
import qualified Named.SimpleM
import qualified Named.Unique
import qualified Unbound.Gen
import qualified Unbound.NonGen
import qualified Unbound.GenV
import qualified Unbound.NonGenV
import qualified Unbound.Lazy.UnboundGenerics
import qualified Unbound.Lazy.UnboundNonGenerics

import Util.Impl (LambdaImpl)

-- | Implementations used in the benchmarking/test suite
-- RHS must be a single variable name for Makefile
-- For Rebound, the key definitions are:
-- Section 2
--    eval_manual_lazy
-- Section 5
--    Table 1: rebound_comparison
--    Table 2: rebound_strict_envV
impls :: [LambdaImpl]
impls = rebound_comparison

---------------------------------------------------------------------------------

-- five benchmarks in Section 2.5
eval_manual_lazy :: [LambdaImpl]
eval_manual_lazy = [
    Rebound.Manual.Lazy.EvalV.impl,
    Rebound.Manual.Lazy.SubstV.impl,
    Rebound.Manual.Lazy.BindV.impl,
    Rebound.Manual.Lazy.EnvV.impl,
    Rebound.Manual.Lazy.ExpSubstV.impl
  ]

-- other related benchmarks that do not appear in the table
eval_manual_other :: [LambdaImpl]
eval_manual_other = [
   Rebound.Manual.Strict.Subst.impl,
   --Rebound.Manual.Strict.SubstV.impl, -- runs out of memory(!)
   Rebound.Manual.Strict.Bind.impl,
   Rebound.Manual.Strict.BindV.impl,
   Rebound.Manual.Strict.Env.impl,
   Rebound.Manual.Strict.EvalV.impl,
   Rebound.Manual.Lazy.ExpSubstEnvV.impl,
   Rebound.Manual.Lazy.Eval.impl,
   Rebound.Manual.Lazy.Subst.impl,
   Rebound.Manual.Lazy.Bind.impl,
   Rebound.Manual.Lazy.Env.impl
  ]

---------------------------------------------------------------------------------

-- Implementations of normal order reduction
-- using both lazy and strict datatype definitions
-- This set generates Table 1 of the rebound paper (Section 5)
rebound_comparison :: [LambdaImpl]
rebound_comparison =
  rebound_strict ++ well_scoped_strict ++ unbound_strict

-- Well-scoped implmentations, libraries plus baseline (Kovacs)
well_scoped_strict :: [LambdaImpl]
well_scoped_strict = [
                NBE.KovacsScoped.impl,
                --Named.FoilV.impl, -- too slow
                DeBruijn.BoundV.impl,
                DeBruijn.Bound.impl,
                Named.Foil.impl
               ]
-- Well-scoped implmentations (unused)
well_scoped_lazy :: [LambdaImpl]
well_scoped_lazy = [
                NBE.Lazy.KovacsScoped.impl,
                Named.Lazy.Foil.impl,
                DeBruijn.Lazy.Nested.impl,
                DeBruijn.Lazy.Bound.impl
               ]

unbound = unbound_strict ++ unbound_lazy
rebound = rebound_strict ++ rebound_lazy

rebound_strict :: [LambdaImpl]
rebound_strict = [
            Rebound.Env.Strict.BindV.impl,
            Rebound.Env.Strict.EnvV.impl,
            Rebound.Env.Strict.EnvGenV.impl,
            Rebound.Env.Strict.Bind.impl,
            Rebound.Env.Strict.Env.impl,
            Rebound.Env.Strict.EnvGen.impl
            ]



rebound_lazy :: [LambdaImpl]
rebound_lazy = [
            Rebound.Env.Lazy.BindV.impl,
            Rebound.Env.Lazy.EnvV.impl,
            Rebound.Env.Lazy.EnvGenV.impl,
            Rebound.Env.Lazy.Bind.impl,
            Rebound.Env.Lazy.Env.impl
            ]


-- these versions using "substBind/instantiate" for beta-reduction
unbound_strict :: [LambdaImpl]
unbound_strict =
  [
    -- Unbound.GenV.impl, -- applicative order, not normal order
    Unbound.Gen.impl, -- unbound-generics
    Unbound.NonGen.impl -- no generic programming
  ]

  -- these versions using "substBind/instantiate" for beta-reduction
unbound_lazy :: [LambdaImpl]
unbound_lazy =
  [
    Unbound.Lazy.UnboundGenerics.impl, -- unbound-generics
    Unbound.Lazy.UnboundNonGenerics.impl -- no generic programming
  ]


---------------------------------------------------------------------------------

-- this is for the "environment representation benchmark"
rebound_strict_envV = [Rebound.Env.Strict.EnvV.impl]

--------------------------------------------------------------------------
-- evaluation only

eval_lazy = eval_manual_lazy ++ eval_auto_lazy

-- analogue to eval_manual_lazy
eval_auto_lazy = [
    Rebound.Env.Lazy.EvalV.impl,
    -- Rebound.Env.Lazy.SubstV.impl, -- much too slow (runs out of memory)
    Rebound.Env.Lazy.BindV.impl,
    Rebound.Env.Lazy.EnvV.impl,
    Rebound.Env.Lazy.ExpSubstV.impl
  ]

--------------------------------------------------------------------------
-- divided by implementation strategy
--
all_impls :: [LambdaImpl]
all_impls =
  all_debruijn ++ all_locallyNameless ++ all_named ++ nbe ++ [Lennart.HOAS.impl]

all_debruijn :: [LambdaImpl]
all_debruijn = rebound -- ++ debruijn ++ debruijn_lazy ++ [Lennart.DeBruijn.impl]

all_locallyNameless :: [LambdaImpl]
all_locallyNameless = locallyNameless ++ locallyNameless_lazy

all_named :: [LambdaImpl]
all_named = named ++ lennart ++ [Lennart.Simple.impl]

--------------------------------------------------------------------------
--------------------------------------------------------------------------


-- divided by lib subdirectory

-- | deBruijn index-based implementations
debruijn :: [LambdaImpl]
debruijn =
  [ -- single substitutions
    DeBruijn.TAPL.impl,
    DeBruijn.Cornell.impl,
    DeBruijn.Lennart.impl,
    DeBruijn.Lift.impl,
    -- parallel substitutions
    DeBruijn.Par.L.impl,
    DeBruijn.Par.Fun.impl,
    DeBruijn.Par.P.impl,
    DeBruijn.Par.B.impl,
    DeBruijn.Par.GB.impl,
    -- Well-scoped single
    DeBruijn.CPDT.impl,
    DeBruijn.Nested.impl,
    DeBruijn.Bound.impl, -- bound
    -- well-scoped parallel
    DeBruijn.Kit.impl,
    DeBruijn.Par.Scoped.impl
    -- DeBruijn.Nested2.impl, --fails test suite
  ]

debruijn_lazy :: [LambdaImpl]
debruijn_lazy =
  [ -- single substitutions
    DeBruijn.Lazy.TAPL.impl,
    DeBruijn.Lazy.Cornell.impl,
    DeBruijn.Lazy.Lift.impl,
    DeBruijn.Lazy.Lennart.impl,
    -- parallel substitutions
    DeBruijn.Lazy.Par.Fun.impl,
    DeBruijn.Lazy.Par.L.impl,
    DeBruijn.Lazy.Par.P.impl,
    DeBruijn.Lazy.Par.B.impl,
    DeBruijn.Lazy.Par.GB.impl,
    -- Well-scoped single
    DeBruijn.Lazy.CPDT.impl,
    DeBruijn.Lazy.Nested.impl,
    DeBruijn.Lazy.Bound.impl, -- bound
    -- Well-scoped parallel
    DeBruijn.Lazy.Kit.impl,
    DeBruijn.Lazy.Par.Scoped.impl
  ]


-- Lennart's original implementations
lennart :: [LambdaImpl]
lennart =
  [ -- Other
    --Lennart.Unique.impl -- buggy
    --Lennart.SimpleOrig.impl -- buggy
    Lennart.Simple.impl,
    Lennart.DeBruijn.impl,
    Lennart.HOAS.impl
  ]

-- | Locally Nameless based implmentations
locallyNameless :: [LambdaImpl]
locallyNameless =
  [ LocallyNameless.Ott.impl,
    LocallyNameless.TypedOtt.impl,
    LocallyNameless.ParScoped.impl,
    LocallyNameless.ParOpt.impl,
    LocallyNameless.Opt.impl,
    LocallyNameless.SupportOpt.impl,
    LocallyNameless.SupportInstOpt.impl,
    LocallyNameless.GenericOpt.impl,
    LocallyNameless.GenericInstOpt.impl,
    LocallyNameless.TypedOpt.impl
  ]

locallyNameless_lazy :: [LambdaImpl]
locallyNameless_lazy =
  [ LocallyNameless.Lazy.Ott.impl,
    LocallyNameless.Lazy.TypedOtt.impl,
    LocallyNameless.Lazy.ParScoped.impl,
    LocallyNameless.Lazy.ParOpt.impl,
    LocallyNameless.Lazy.Opt.impl,
    LocallyNameless.Lazy.SupportOpt.impl,
    LocallyNameless.Lazy.GenericOpt.impl
  ]


-- | Name based/nominal implementations
named :: [LambdaImpl]
named =
  [ Named.SimpleH.impl,
    Named.SimpleGH.impl,
    Named.SimpleM.impl,
    Named.Lennart.impl,
    Named.Simple.impl,
    Named.Unique.impl,
    Named.Foil.impl
    -- Named.Nom -- too slow
    -- Named.NominalG -- too slow
  ]

named_lazy :: [LambdaImpl]
named_lazy =
  [ Named.Lazy.SimpleH.impl,
    Named.Lazy.SimpleGH.impl,
    Named.Lazy.SimpleM.impl,
    Named.Lazy.Foil.impl
    -- Named.Lazy.NominalG -- too slow
  ]


nbe :: [LambdaImpl]
nbe =
  [ NBE.Aelig.impl,
    -- NBE.Boesflug.impl, -- hangs on full
    -- NBE.Felgenhauer.impl, -- wonky
    NBE.Kovacs.impl,
    NBE.KovacsNamed.impl,
    NBE.KovacsScoped.impl
    --DeBruijn.Krivine.impl,   -- slower than the rest
    --DeBruijn.KrivineScoped.impl -- slower than the rest
  ]

---------------------------------------------------
---------------------------------------------------
-- implementations divided by source

-- implementations available on hackage
hackage :: [LambdaImpl]
hackage =
  [ -- Named.Nom.impl, -- https://hackage.haskell.org/package/nom
    -- really, really slow.
    Named.NominalG.impl, -- nominal, generally too slow (12s vs. <200 ms for everything else)
    -- https://hackage.haskell.org/package/nominal
    Named.Lazy.NominalG.impl,
    Unbound.Gen.impl, -- unbound-generics
    DeBruijn.Bound.impl, -- bound
    DeBruijn.Lazy.Bound.impl, -- bound
    Named.Foil.impl,
    Named.Lazy.Foil.impl -- free-foil
  ]

---------------------------------------------------

