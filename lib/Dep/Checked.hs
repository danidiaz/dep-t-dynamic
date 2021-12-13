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
-- An environment which records the dependencies of all components that are added to it, allowing you to check if all
-- dependencies are satisfied before running the program logic.
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
import qualified Algebra.Graph.Bipartite.Undirected.AdjacencyMap as Bipartite

data CheckedEnv phases rune_ m = CheckedEnv DepGraph (DynamicEnv phases (DepT rune_ m))

-- | Add a component to a 'CheckedEnv'.
--
-- __TYPE APPLICATIONS REQUIRED__. You must provide three types using @TypeApplications@:
--
-- * The type @r_@ of the parameterizable record we want to add to the environment.
--
-- * The type-level list @rs@ of the component types the @r_@ value depends on (might be empty).
--
-- * The type-level list @mcs@ of the constraints the @r_@ value requires from the base monad (might be empty).
--
-- It's impossible to add a component without explicitly listing all its dependencies. 
--
-- In addition, you must also provide the @phases (r_ (DepT e_ n))@ value, an implementation of the component that comes
-- wrapped in some 'Applicative' phase. Notice that this value must be sufficiently polymorphic.
--
-- The @QuantifiedConstraint@ says that, whatever the environment the 'DepT' uses, if @DynamicEnv Identity n@ has a 'Has'
-- constraint, the 'DepT' environment must also have that constraint. This is trivially true when they are the same type,
-- but may also be true when the 'DepT' environment wraps the 'DynamicEnv' and defines passthrough 'Has' instances.
checkedDep ::
  forall r_ rs mcs phases rune_ m.
  ( SOP.All R.Typeable rs,
    SOP.All R.Typeable mcs,
    R.Typeable r_,
    R.Typeable phases,
    R.Typeable rune_,
    R.Typeable m,
    HasAll rs (DepT rune_ m) (rune_ (DepT rune_ m)),
    forall s_ z n. Has s_ n (DynamicEnv Identity n) => Has s_ n (rune_ n),
    Monad m,
    MonadSatisfiesAll mcs (DepT rune_ m)
  ) =>
  -- | stuff
  ( forall e_ n.
    ( HasAll rs (DepT e_ n) (e_ (DepT e_ n)),
      Monad n, 
      MonadSatisfiesAll mcs (DepT e_ n)
    ) =>
    phases (r_ (DepT e_ n))
  ) ->
  -- | stuff
  CheckedEnv phases rune_ m ->
  CheckedEnv phases rune_ m
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
   in CheckedEnv depGraph' (insertDep (f @rune_) de)

-- | '(<>)' might result in over-restrictive dependency graphs, because
-- dependencies for colliding components are kept even as only one of the
-- components is kept.
instance Semigroup (CheckedEnv phases rune_ m) where
  CheckedEnv g1 env1 <> CheckedEnv g2 env2 = CheckedEnv (g1 <> g2) (env1 <> env2)

-- | 'mempty' is for creating the empty environment.
instance Monoid (CheckedEnv phases rune_ m) where
  mempty = CheckedEnv mempty mempty

getUnchecked :: CheckedEnv phases rune_ m -> (DepGraph, DynamicEnv phases (DepT rune_ m))
getUnchecked (CheckedEnv g d) = (g, d)

checkEnv :: CheckedEnv phases rune_ m -> Either (HashSet SomeDepRep) (DepGraph, DynamicEnv phases (DepT rune_ m))
checkEnv (CheckedEnv g@DepGraph {required,provided} d) = 
  let missing = HashSet.difference required provided 
   in if HashSet.null missing
      then Right (g, d)
      else Left missing
