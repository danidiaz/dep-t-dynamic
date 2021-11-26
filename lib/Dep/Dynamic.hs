-- | This module provies a dynamic version of a dependency injection
-- environment.
--
-- You don't need to declare beforehand what fields exist in the environment,
-- you can simply add the components directly.
--
-- It's not checked at compilation time that the dependencies for all
-- components in the environment are also present in the environment. A
-- `DynamicEnv` exception will be thrown at run time when a component tries to
-- find a dependency that doesn't exist.
module Dep.Dynamic
  (
  -- * A dynamic environment
    DynamicEnv
  , insertDep
  , deleteDep
  , DepNotFound (..)
  -- * Re-exports
  , mempty
  )
where

import Dep.Dynamic.Internal
import Data.Monoid


