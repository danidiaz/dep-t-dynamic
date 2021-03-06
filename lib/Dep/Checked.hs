{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}

-- | __NOTE__: This module can only be used when your dependencies live in the 'Control.Monad.Dep.DepT' monad. 
-- Use 'Dep.SimpleChecked' instead when dependencies are handled in an 'Dep.Env.Constructor' phase.
--
-- This module provides an environment which tracks the dependencies of
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
--  env :: CheckedEnv Identity (DynamicEnv Identity) IO
--  env = mempty 
--      & checkedDep @Foo @'[]    @'[MonadIO] (Identity (component \_ -> makeIOFoo))
--      & checkedDep @Bar @'[Foo] @'[]        (Identity (component makeBar)) 
--  envReady :: DynamicEnv Identity (DepT (DynamicEnv Identity) IO)
--  envReady = 
--    let Right (_, checked) = checkEnv env
--     in checked
-- :}
--
-- >>> :{
--  runFromDep (pure envReady) bar "this is bar"
-- :}
-- this is bar
--
-- An example of a failed check:
--
-- >>> :{
--  badEnv :: CheckedEnv Identity (DynamicEnv Identity) IO
--  badEnv = mempty 
--      & checkedDep @Bar @'[Foo] @'[] (Identity (component makeBar)) 
-- :}
--
-- >>> :{
--  let Left missing = checkEnv badEnv
--   in missing
-- :}
-- fromList [Foo]
--
module Dep.Checked
  (
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

import Control.Monad.Dep
import Data.Functor.Compose
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Hashable
import Data.Kind
import Data.Proxy
import Data.SOP (K (..))
import Data.SOP qualified as SOP
import Data.SOP.NP
import Dep.Dynamic
import Dep.Dynamic.Internal
import Dep.Has
import Dep.Env
import GHC.TypeLits
import Type.Reflection qualified as R
import Data.Functor
import Algebra.Graph 
import qualified Algebra.Graph.Bipartite.AdjacencyMap as Bipartite

-- | A dependency injection environment for components with effects in the monad @(DepT me_ m)@.
-- Parameterized by an 'Applicative' phase @h@, the environment type constructor
-- @me_@ used by the 'DepT' transformer, and the type @m@ of the base
-- monad.
data CheckedEnv h me_ m = CheckedEnv DepGraph (DynamicEnv h (DepT me_ m))

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
-- In addition, you must also provide the @h (r_ (DepT e_ n))@ value, an implementation of the component that comes
-- wrapped in some 'Applicative'. Notice that this value must be sufficiently polymorphic.
--
-- The @QuantifiedConstraint@ says that, whatever the environment the 'DepT' uses, if @DynamicEnv Identity n@ has a 'Has'
-- constraint, the 'DepT' environment must also have that constraint. This is trivially true when they are the same type,
-- but may also be true when the 'DepT' environment wraps the 'DynamicEnv' and defines passthrough 'Has' instances.
checkedDep ::
  forall r_ rs mcs h me_ m.
  ( SOP.All R.Typeable rs,
    SOP.All R.Typeable mcs,
    R.Typeable r_,
    R.Typeable h,
    R.Typeable me_,
    R.Typeable m,
    HasAll rs (DepT me_ m) (me_ (DepT me_ m)),
    forall s_ z n. Has s_ n (DynamicEnv Identity n) => Has s_ n (me_ n),
    Monad m,
    MonadSatisfiesAll mcs (DepT me_ m)
  ) =>
  -- | The wrapped component
  ( forall e_ n.
    ( HasAll rs (DepT e_ n) (e_ (DepT e_ n)),
      Monad n, 
      MonadSatisfiesAll mcs (DepT e_ n)
    ) =>
    h (r_ (DepT e_ n))
  ) ->
  -- | The environment in which to insert
  CheckedEnv h me_ m ->
  CheckedEnv h me_ m
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
   in CheckedEnv depGraph' (insertDep (f @me_) de)

-- | '(<>)' might result in over-restrictive dependency graphs, because
-- dependencies for colliding components are kept even as only one of the
-- components is kept.
instance Semigroup (CheckedEnv h me_ m) where
  CheckedEnv g1 env1 <> CheckedEnv g2 env2 = CheckedEnv (g1 <> g2) (env1 <> env2)

-- | 'mempty' is for creating the empty environment.
instance Monoid (CheckedEnv h me_ m) where
  mempty = CheckedEnv mempty mempty

-- | Extract the underlying 'DynamicEnv' along with the dependency graph, without checking that all dependencies are satisfied.
getUnchecked :: CheckedEnv h me_ m -> (DepGraph, DynamicEnv h (DepT me_ m))
getUnchecked (CheckedEnv g d) = (g, d)

-- | Either fail with a the set of missing dependencies, or
-- succeed and produce the the underlying 'DynamicEnv' along with the
-- dependency graph.
checkEnv :: CheckedEnv h me_ m -> Either (HashSet SomeDepRep) (DepGraph, DynamicEnv h (DepT me_ m))
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
-- >>> import Dep.Has
-- >>> import Dep.Env
-- >>> import Dep.Dynamic
-- >>> import Dep.Checked
-- >>> import Dep.Advice (component, runFromDep)
