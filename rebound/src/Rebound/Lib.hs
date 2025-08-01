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
    -- module Data.Nat,
    -- module Data.SNat,
    Nat(Z,S), 
    module Data.SNat,
    Fin_(..), fin_, f0, f1, f2, fs,
    Vec_(..), vec_, (|>),
  )
where

import Data.Fin
import Data.Kind (Type)
import Data.SNat
import Data.Type.Equality
import Data.Vec
