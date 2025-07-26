-- imports and reexports libraries for Dependent Haskell
-- Because Fin and Vec include definitions with the same
-- name as Prelude functions, clients of this module should also 
--    import Data.Fin qualified as Fin
--    import Data.Vec qualified as Vec
module Rebound.Lib
  ( 
    type Type,
    module Data.Type.Equality,
    Fin (..),
    Vec (..),
    ToInt (..),
    module Data.Nat,
    module Data.SNat,
  )
where

import Data.Fin (Fin (..))
import Data.Kind (Type)
import Data.Nat
import Data.SNat
import Data.Type.Equality
import Data.Vec (Vec (..))
