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
-- >>> :{
--  newtype Foo d = Foo {foo :: String -> d ()}
--  newtype Bar d = Bar {bar :: String -> d ()}
--  makeIOFoo :: MonadIO m => Foo m
--  makeIOFoo = Foo (liftIO . putStrLn)
--  makeBar :: Has Foo m env => env -> Bar m
--  makeBar (asCall -> call) = Bar (call foo)
--  env :: DynamicEnv (Constructor (DynamicEnv Identity IO)) IO
--  env = mempty 
--      & insertDep @Foo (fromBare (\_ -> makeIOFoo))
--      & insertDep @Bar (fromBare makeBar) 
--  envReady :: DynamicEnv Identity IO
--  envReady = fixEnv env
-- :}
--
-- >>> :{
--  bar (dep envReady) "this is bar"
-- :}
-- this is bar
--
-- Components are found by type. Use "Dep.Tagged" to disambiguate components of
-- the same type.
--
-- It's not checked at compilation time that the dependencies for all
-- components in the environment are also present in the environment. A
-- `DynamicEnv` exception will be thrown at run time whenever a component tries to
-- find a dependency that doesn't exist. See `Dep.Checked` and `Dep.SimpleChecked` for safer (but still dynamically typed) approaches.
module Dep.Dynamic
  (
  -- * A dynamic environment
    DynamicEnv
  , insertDep
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

-- $setup
--
-- >>> :set -XTypeApplications
-- >>> :set -XMultiParamTypeClasses
-- >>> :set -XImportQualifiedPost
-- >>> :set -XStandaloneKindSignatures
-- >>> :set -XNamedFieldPuns
-- >>> :set -XFunctionalDependencies
-- >>> :set -XFlexibleContexts
-- >>> :set -XDataKinds
-- >>> :set -XBlockArguments
-- >>> :set -XFlexibleInstances
-- >>> :set -XTypeFamilies
-- >>> :set -XDeriveGeneric
-- >>> :set -XViewPatterns
-- >>> :set -XScopedTypeVariables
-- >>> import Data.Kind
-- >>> import Control.Monad.Dep
-- >>> import Dep.Has
-- >>> import Dep.Env
-- >>> import Dep.Dynamic
-- >>> import Data.Function
--