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

module Dep.Checked
  (
  CheckedEnv,
  checkedDep,
  getUnchecked,
  checkEnv,
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

checkedDep ::
  forall rs mcs r_ phases rune_ m.
  ( SOP.All R.Typeable rs,
    SOP.All R.Typeable mcs,
    R.Typeable r_,
    R.Typeable phases,
    R.Typeable rune_,
    R.Typeable m,
    HasAll rs (DepT rune_ m) (rune_ (DepT rune_ m)),
    forall s_ z n. Has s_ n (DynamicEnv Identity n) => Has s_ n (rune_ n),
    MonadSatisfiesAll mcs (DepT rune_ m)
  ) =>
  -- | stuff
  ( forall e_ n.
    ( HasAll rs (DepT e_ n) (e_ (DepT e_ n)),
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

instance Semigroup (CheckedEnv phases rune_ m) where
  CheckedEnv g1 env1 <> CheckedEnv g2 env2 = CheckedEnv (g1 <> g2) (env1 <> env2)

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
