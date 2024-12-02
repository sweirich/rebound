module AutoEnv.Pat.Rebind where

import AutoEnv.Classes
import AutoEnv.Env
import AutoEnv.Lib
import AutoEnv.Pat

----------------------------------------------------------
-- Rebind
----------------------------------------------------------

data Rebind p1 p2 n where
  Rebind :: p1 n -> p2 (Plus (Size p1) n) -> Rebind p1 p2 n

instance (Sized p1, Sized p2) => Sized (Rebind p1 p2) where
  type Size (Rebind p1 p2) = Plus (Size p2) (Size p1)
  size :: Rebind p1 p2 n -> SNat (Plus (Size p2) (Size p1))
  size (Rebind p1 p2) = sPlus (size p2) (size p1)

instance
  (Subst v v, Sized p1, Subst v p1, Subst v p2) =>
  Subst v (Rebind p1 p2)
  where
  applyE ::
    (Subst v v, Sized p1, Subst v p1, Subst v p2) =>
    Env v n m ->
    Rebind p1 p2 n ->
    Rebind p1 p2 m
  applyE r (Rebind p1 p2) = Rebind (applyE r p1) (applyE (upN (size p1) r) p2)

instance (Sized p1, FV p1, FV p2) => FV (Rebind p1 p2) where
  appearsFree :: (Sized p1, FV p1, FV p2) => Fin n -> Rebind p1 p2 n -> Bool
  appearsFree n (Rebind p1 p2) = appearsFree n p1 || appearsFree (shiftN (size p1) n) p2

instance (Sized p1, Strengthen p1, Strengthen p2) => Strengthen (Rebind p1 p2) where
  strengthen' ::
    forall m n p.
    SNat m ->
    SNat n ->
    Rebind p1 p2 (Plus m n) ->
    Maybe (Rebind p1 p2 n)
  strengthen' m n (Rebind p1 p2) =
    case axiomM @m @(Size p1) @n of
      Refl ->
        Rebind
          <$> strengthen' m n p1
          <*> strengthen' m (sPlus (size p1) n) p2

unRebind ::
  forall p1 p2 n c.
  (Sized p1, Sized p2, SNatI n) =>
  Rebind p1 p2 n ->
  ( ( SNatI (Size p1),
      SNatI (Size p2),
      SNatI (Plus (Size p1) n),
      Plus (Size p2) (Plus (Size p1) n) ~ Plus (Plus (Size p2) (Size p1)) n
    ) =>
    p1 n ->
    p2 (Plus (Size p1) n) ->
    c
  ) ->
  c
unRebind (Rebind p1 p2) f =
  case axiomAssoc @(Size p2) @(Size p1) @n of
    Refl ->
      withSNat (size p1) $
        withSNat (size p2) $
          withSNat (sPlus (size p1) (snat @n)) $
            f p1 p2