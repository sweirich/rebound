module Rebound.Scoped (EqSized (..), ScopedSized (..)) where

import Rebound
import Data.Vec (Vec((:::)), empty)

----------------------------------------------------------
-- Sized type class for patterns
----------------------------------------------------------

-- Scoped patterns have kinds :: Nat -> Nat -> Type where
-- the first parameter is `p`, the number of variables that pattern
-- binds, and the second parameter is `n`, the scope of for any
-- terms that appear inside the pattern.

-- Crucially, the number of variables bound by the pattern
-- shouldn't depend on the scope. We manifest that with the
-- associated type `ScopedSize :: Nat -> Type` and the constraint
-- that it must be the same as Size for any number of bound variables.

class (Sized (t p), Size (t p) ~ ScopedSize t) => EqSized t p

instance (Sized (t p), Size (t p) ~ ScopedSize t) => EqSized t p

-- this is equivalent to (Size (t p) ~ ScopedSize pat
class (forall p. EqSized pat p) => ScopedSized pat where
  type ScopedSize (pat :: Nat -> Type) :: Nat

-- class Scope v s | s -> v where
--   extend :: s n -> v n -> s (S n)