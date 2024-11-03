-- imports and reexports libraries for Nat / Fin / Vec
module Lib(module Nat,
           module Fin,
           type Type,
           Vec(..),
           Sized(..)) where

import Data.Kind(Type)
import Nat
import Fin
import Vec

-----------------------------------------------------
-- Statically sized types

class Sized t where
    type Size t :: Nat
    size :: t -> SNat (Size t)

instance Sized (SNat n) where
    type Size (SNat n) = n
    size = id

instance SNatI n => Sized (Vec n a) where
    type Size (Vec n a) = n
    size _ = snat
    