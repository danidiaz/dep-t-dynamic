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

-- | This module provides an environment which tracks the dependencies of all
-- components that are added to it, allowing you to check if all
-- dependencies
-- are satisfied before running the program logic.
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

data CheckedEnv phases m = CheckedEnv DepGraph (DynamicEnv (phases `Compose` Constructor (DynamicEnv Identity m)) m)

checkedDep ::
  forall r_ rs mcs phases m.
  ( SOP.All R.Typeable rs,
    SOP.All R.Typeable mcs,
    R.Typeable r_,
    R.Typeable phases,
    R.Typeable m,
    HasAll rs m (DynamicEnv Identity m),
    Monad m, 
    MonadSatisfiesAll mcs m
  ) =>
  -- | stuff
  ( forall e n.
    ( HasAll rs n e,
      Monad m, 
      MonadSatisfiesAll mcs n
    ) =>
    (phases `Compose` Constructor e) (r_ n)
  ) ->
  -- | stuff
  CheckedEnv phases m ->
  CheckedEnv phases m
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
instance Semigroup (CheckedEnv phases m) where
  CheckedEnv g1 env1 <> CheckedEnv g2 env2 = CheckedEnv (g1 <> g2) (env1 <> env2)

-- | 'mempty' is for creating the empty environment.
instance Monoid (CheckedEnv phases m) where
  mempty = CheckedEnv mempty mempty

getUnchecked :: CheckedEnv phases m -> (DepGraph, DynamicEnv (phases `Compose` Constructor (DynamicEnv Identity m)) m)
getUnchecked (CheckedEnv g d) = (g, d)

checkEnv :: CheckedEnv phases m -> Either (HashSet SomeDepRep) (DepGraph, DynamicEnv (phases `Compose` Constructor (DynamicEnv Identity m)) m)
checkEnv (CheckedEnv g@DepGraph {required,provided} d) = 
  let missing = HashSet.difference required provided 
   in if HashSet.null missing
      then Right (g, d)
      else Left missing

-- phaselessDep (no phases, only the constructor)
--
