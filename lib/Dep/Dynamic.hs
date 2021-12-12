-- | This module provies a dynamic version of a dependency injection
-- environment.
--
-- You don't need to declare beforehand what fields exist in the environment,
-- you can simply add them using 'insertDep'.
--
-- I might be useful for quick prototyping, or for when there is a big number
-- of components and putting all of them in a conventional record would slow
-- compilation.
--
-- Components are found by type. Use "Dep.Tagged" to disambiguate components of
-- the same type.
--
-- It's not checked at compilation time that the dependencies for all
-- components in the environment are also present in the environment. A
-- `DynamicEnv` exception will be thrown at run time whenever a component tries to
-- find a dependency that doesn't exist.
module Dep.Dynamic
  (
  -- * A dynamic environment
    DynamicEnv
  , insertDep
  , insertBareDep
  , deleteDep
  , DepNotFound (..)
  , SomeDepRep (..)
  , depRep
  -- * Helpers for defining phases
  , Bare
  , fromBare
  , toBare
  -- * Re-exports
  , mempty
  )
where

import Dep.Dynamic.Internal
import Data.Monoid


