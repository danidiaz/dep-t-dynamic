{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BlockArguments #-}

-- | This module provides an environment which tracks the dependencies of
-- components that are added to it, allowing you to check if all
-- dependencies
-- are satisfied before running the program logic.
--
-- >>> :{
--  newtype Foo d = Foo {foo :: String -> d ()} deriving Generic
--  newtype Bar d = Bar {bar :: String -> d ()} deriving Generic
--  makeIOFoo :: MonadIO m => Foo m
--  makeIOFoo = Foo (liftIO . putStrLn)
--  makeBar :: Has Foo m env => env -> Bar m
--  makeBar (asCall -> call) = Bar (call foo)
--  env :: CheckedEnv Identity IO
--  env = mempty 
--      & checkedDep @Foo @'[]    @'[MonadIO] (fromBare (\_ -> makeIOFoo))
--      & checkedDep @Bar @'[Foo] @'[]        (fromBare makeBar) 
--  envReady :: DynamicEnv Identity IO
--  envReady = 
--    let Right (_, pullPhase -> Identity checked) = checkEnv env
--     in fixEnv checked
-- :}
--
-- >>> :{
--  bar (dep envReady) "this is bar"
-- :}
-- this is bar
--
-- An example of a failed check:
--
-- >>> :{
--  badEnv :: CheckedEnv Identity IO
--  badEnv = mempty 
--      & checkedDep @Bar @'[Foo] @'[] (fromBare makeBar) 
-- :}
--
-- >>> :{
--  let Left missing = checkEnv badEnv
--   in missing
-- :}
-- fromList [Foo]
--
module Dep.SimpleChecked (
  -- * A checked environment
  CheckedEnv,
  checkedDep,
  getUnchecked,
  checkEnv,
  -- * The dependency graph
  DepGraph (..),
  SomeMonadConstraintRep (..),
  monadConstraintRep,
  -- * Re-exports
  mempty
) where

import Data.Functor.Compose
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Hashable
import Data.Kind
import Data.Proxy
import Data.SOP (K (..))
import Data.SOP qualified as SOP
import Data.SOP.NP
import Dep.Has
import Dep.Dynamic
import Dep.Dynamic.Internal
import Dep.Env
import GHC.TypeLits
import Type.Reflection qualified as R
import Data.Functor
import Algebra.Graph 
import qualified Algebra.Graph.Bipartite.Undirected.AdjacencyMap as Bipartite

-- | A dependency injection environment for components with effects in the monad @m@.
-- Parameterized by an 'Applicative' phase @h@, and the type @m@ of the effect monad.
data CheckedEnv h m = CheckedEnv DepGraph (DynamicEnv (h `Compose` Constructor (DynamicEnv Identity m)) m)

-- | Add a component to a 'CheckedEnv'.
--
-- __TYPE APPLICATIONS REQUIRED__. You must provide three types using @TypeApplications@:
--
-- * The type @r_@ of the parameterizable record we want to add to the environment.
--
-- * The type-level list @rs@ of the components the @r_@ value depends on (might be empty).
--
-- * The type-level list @mcs@ of the constraints the @r_@ value requires from the base monad (might be empty).
--
-- It's impossible to add a component without explicitly listing all its dependencies. 
--
-- In addition, you must also provide the @(h `Compose` Constructor e)@ value, an implementation of the component that comes
-- wrapped in some 'Applicative'. Notice that this value must be sufficiently polymorphic.
checkedDep ::
  forall r_ rs mcs h m.
  ( SOP.All R.Typeable rs,
    SOP.All R.Typeable mcs,
    R.Typeable r_,
    R.Typeable h,
    R.Typeable m,
    HasAll rs m (DynamicEnv Identity m),
    Monad m, 
    MonadSatisfiesAll mcs m
  ) =>
  -- | The wrapped component
  ( forall e n.
    ( HasAll rs n e,
      Monad m, 
      MonadSatisfiesAll mcs n
    ) =>
    (h `Compose` Constructor e) (r_ n)
  ) ->
  -- | The environment in which to insert
  CheckedEnv h m ->
  CheckedEnv h m
checkedDep f (CheckedEnv DepGraph {provided,required,depToDep,depToMonad} de) =
  let demoteDep :: forall (x :: (Type -> Type) -> Type). R.Typeable x => K SomeDepRep x
      demoteDep = K (depRep @x)
      depReps = collapse_NP $ cpure_NP @R.Typeable @rs Proxy demoteDep
      demoteMonadConstraint :: forall (x :: (Type -> Type) -> Constraint). R.Typeable x => K SomeMonadConstraintRep x
      demoteMonadConstraint = K (SomeMonadConstraintRep (R.typeRep @x))
      monadConstraintReps = collapse_NP $ cpure_NP @R.Typeable @mcs Proxy demoteMonadConstraint
      provided' = HashSet.insert (depRep @r_) provided 
      required' = foldr HashSet.insert required depReps
      depGraph' = DepGraph {
            provided = provided'
        ,   required = required'
        ,   depToDep = overlay depToDep $ edges $ (depRep @r_,) <$> depReps
        ,   depToMonad = Bipartite.overlay depToMonad $ Bipartite.edges $ (depRep @r_,) <$> monadConstraintReps
        }
   in CheckedEnv depGraph' (insertDep (f @(DynamicEnv Identity m) @m) de)

-- | '(<>)' might result in over-restrictive dependency graphs, because
-- dependencies for colliding components are kept even as only one of the
-- components is kept.
instance Semigroup (CheckedEnv h m) where
  CheckedEnv g1 env1 <> CheckedEnv g2 env2 = CheckedEnv (g1 <> g2) (env1 <> env2)

-- | 'mempty' is for creating the empty environment.
instance Monoid (CheckedEnv h m) where
  mempty = CheckedEnv mempty mempty

-- | Extract the underlying 'DynamicEnv' along with the dependency graph, without checking that all dependencies are satisfied.
getUnchecked :: CheckedEnv h m -> (DepGraph, DynamicEnv (h `Compose` Constructor (DynamicEnv Identity m)) m)
getUnchecked (CheckedEnv g d) = (g, d)

-- | Either fail with a the set of missing dependencies, or
-- succeed and produce the the underlying 'DynamicEnv' along with the
-- dependency graph.
checkEnv :: CheckedEnv h m -> Either (HashSet SomeDepRep) (DepGraph, DynamicEnv (h `Compose` Constructor (DynamicEnv Identity m)) m)
checkEnv (CheckedEnv g@DepGraph {required,provided} d) = 
  let missing = HashSet.difference required provided 
   in if HashSet.null missing
      then Right (g, d)
      else Left missing

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
-- >>> import Data.Function
-- >>> import GHC.Generics (Generic)
-- >>> import Data.Either
-- >>> import Dep.Has
-- >>> import Dep.Env
-- >>> import Dep.Dynamic
-- >>> import Dep.SimpleChecked
-- >>> import Dep.Advice (component, runFromDep)
