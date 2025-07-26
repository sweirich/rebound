module Rebound.Generics where
    
import GHC.Generics hiding (S)
import Rebound.Env
import Rebound.Classes
import Data.Set qualified as Set
--------------------------------------------
-- Generic implementation of Subst class
--------------------------------------------

-- Constant types
instance GSubst v (K1 i c) where
  gsubst s (K1 c) = K1 c
  {-# INLINE gsubst #-}

instance GSubst v U1 where
  gsubst _s U1 = U1
  {-# INLINE gsubst #-}

instance (GSubst b f) => GSubst b (M1 i c f) where
  gsubst s = M1 . gsubst s . unM1
  {-# INLINE gsubst #-}

instance GSubst b V1 where
  gsubst _s = error "BUG: void type"
  {-# INLINE gsubst #-}

instance (GSubst b f, GSubst b g) => GSubst b (f :*: g) where
  gsubst s (f :*: g) = gsubst s f :*: gsubst s g
  {-# INLINE gsubst #-}

instance (GSubst b f, GSubst b g) => GSubst b (f :+: g) where
  gsubst s (L1 f) = L1 $ gsubst s f
  gsubst s (R1 g) = R1 $ gsubst s g
  {-# INLINE gsubst #-}

instance (Subst b g) => GSubst b (Rec1 g) where
  gsubst s (Rec1 f) = Rec1 (applyE s f)
  {-# INLINE gsubst #-}

--------------------------------------------
-- Generic implementation of FV class
--------------------------------------------

instance (FV t) => GFV (Rec1 t) where
  gappearsFree s (Rec1 f) = appearsFree s f
  {-# INLINE gappearsFree #-}
  gfreeVars (Rec1 f) = freeVars f
  {-# INLINE gfreeVars #-}

-- Constant types
instance GFV (K1 i c) where
  gappearsFree s (K1 c) = False
  {-# INLINE gappearsFree #-}
  gfreeVars (K1 c) = Set.empty
  {-# INLINE gfreeVars #-}

instance GFV U1 where
  gappearsFree _s U1 = False
  {-# INLINE gappearsFree #-}
  gfreeVars U1 = Set.empty

instance GFV f => GFV (M1 i c f) where
  gappearsFree s = gappearsFree s . unM1
  {-# INLINE gappearsFree #-}
  gfreeVars = gfreeVars . unM1
  {-# INLINE gfreeVars #-}

instance GFV V1 where
  gappearsFree _s = error "BUG: void type"
  {-# INLINE gappearsFree #-}
  gfreeVars v = error "BUG: void type"
  {-# INLINE gfreeVars #-}

instance (GFV f, GFV g) => GFV (f :*: g) where
  gappearsFree s (f :*: g) = gappearsFree s f && gappearsFree s g
  {-# INLINE gappearsFree #-}
  gfreeVars (f :*: g) = gfreeVars f <> gfreeVars g
  {-# INLINE gfreeVars #-}

instance (GFV f, GFV g) => GFV (f :+: g) where
  gappearsFree s (L1 f) = gappearsFree s f
  gappearsFree s (R1 g) = gappearsFree s g
  {-# INLINE gappearsFree #-}

  gfreeVars (L1 f) = gfreeVars f
  gfreeVars (R1 g) = gfreeVars g
  {-# INLINE gfreeVars #-}

------------------------------------------------
-- Generic implementation of Strengthening class
------------------------------------------------



instance GStrengthen (K1 i c) where
  gstrengthenRec m n k (K1 c) = pure (K1 c)
  {-# INLINE gstrengthenRec #-}

instance GStrengthen U1 where
  gstrengthenRec m n k U1 = pure U1
  {-# INLINE gstrengthenRec #-}

instance GStrengthen f => GStrengthen (M1 i c f) where
  gstrengthenRec m n k x = M1 <$> gstrengthenRec m n k (unM1 x)
  {-# INLINE gstrengthenRec #-}

instance GStrengthen V1 where
  gstrengthenRec m n k = error "BUG: void type"
  {-# INLINE gstrengthenRec #-}

instance (GStrengthen f, GStrengthen g) => GStrengthen (f :*: g) where
  gstrengthenRec m n k (f :*: g) = (:*:) <$> gstrengthenRec m n k f <*> gstrengthenRec m n k g
  {-# INLINE gstrengthenRec #-}

instance (GStrengthen f, GStrengthen g) => GStrengthen (f :+: g) where
  gstrengthenRec m n k (L1 f) = L1 <$> gstrengthenRec m n k f
  gstrengthenRec m n k (R1 g) = R1 <$> gstrengthenRec m n k g
  {-# INLINE gstrengthenRec #-}

instance Strengthen t => GStrengthen (Rec1 t) where
  gstrengthenRec k m n (Rec1 t) = Rec1 <$> strengthenRec k m n t