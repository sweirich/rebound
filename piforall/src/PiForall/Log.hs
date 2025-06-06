module PiForall.Log (Log (..), isInfo) where

import Control.Monad.Writer (MonadWriter (tell))
import Data.List qualified as List

data Log
  = Info String
  | Warn String

instance Show Log where
  show (Info s) = "info: " <> s
  show (Warn s) = "warn:\n" <> s

isInfo :: Log -> Bool
isInfo (Info _) = True
isInfo _ = False

-- info = tell . List.singleton . Info
-- warn = tell . List.singleton . Warn