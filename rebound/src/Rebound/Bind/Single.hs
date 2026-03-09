-- |
-- Module       : Rebound.Bind.Single
-- Description  : Bind a single variable, without metadata
--
-- Simplest form of binding: a single variable with no other information stored with the binder.
-- This is a specialization of "Rebound.Bind.PatN".
module Rebound.Bind.Single
  ( module Rebound,
    Bind (..),
    bind,
    unbind,
    unbindl,
    getBody,
    instantiate,
    bindWith,
    unbindWith,
    instantiateWith,
    applyUnder,
  )
where

import Rebound
import Rebound.Bind.PatN
import Rebound.Classes
