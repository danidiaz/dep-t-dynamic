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

module Dep.SimpleChecked where

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
import Dep.Env
import GHC.TypeLits
import Type.Reflection qualified as R
import Algebra.Graph 
import qualified Algebra.Graph.Bipartite.Undirected.AdjacencyMap as Bipartite

data CheckedEnv phases m = CheckedEnv DepGraph (DynamicEnv (phases `Compose` Constructor (DynamicEnv Identity m)) m)

type HasAll :: [(Type -> Type) -> Type] -> (Type -> Type) -> Type -> Constraint
type family HasAll rs m e where
  HasAll '[] m e = ()
  HasAll (r_ : rs) m e = (Has r_ m e, HasAll rs m e)

type MonadSatisfiesAll :: [(Type -> Type) -> Constraint] -> (Type -> Type) -> Constraint
type family MonadSatisfiesAll cs m where
  MonadSatisfiesAll '[] m = ()
  MonadSatisfiesAll (c : cs) m = (c m, MonadSatisfiesAll cs m)

checkedDep ::
  forall rs mcs r_ m phases.
  ( SOP.All R.Typeable rs,
    SOP.All R.Typeable mcs,
    R.Typeable r_,
    R.Typeable m,
    R.Typeable phases,
    HasAll rs m (DynamicEnv Identity m),
    MonadSatisfiesAll mcs m
  ) =>
  -- | stuff
  ( forall e n.
    ( HasAll rs n e,
      MonadSatisfiesAll mcs n
    ) =>
    (phases `Compose` Constructor e) (r_ n)
  ) ->
  -- | stuff
  CheckedEnv phases m ->
  CheckedEnv phases m
checkedDep f (CheckedEnv (DepGraph {provided,required,depToDep,depToMonad}) de) =
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
        ,   depToDep = undefined
        ,   depToMonad = undefined
        }
   in CheckedEnv depGraph' (insertDep (f @(DynamicEnv Identity m) @m) de)

data SomeMonadConstraintRep where
  SomeMonadConstraintRep :: forall (a :: (Type -> Type) -> Constraint). !(R.TypeRep a) -> SomeMonadConstraintRep

instance Eq SomeMonadConstraintRep where
    SomeMonadConstraintRep r1 == SomeMonadConstraintRep r2 = R.SomeTypeRep r1 == R.SomeTypeRep r2

instance Ord SomeMonadConstraintRep where
    SomeMonadConstraintRep r1 `compare` SomeMonadConstraintRep r2 = R.SomeTypeRep r1 `compare` R.SomeTypeRep r2

instance Hashable SomeMonadConstraintRep where
  hashWithSalt salt (SomeMonadConstraintRep tr) = hashWithSalt salt tr
  hash (SomeMonadConstraintRep tr) = hash tr

data DepGraph = DepGraph
  { provided :: HashSet SomeDepRep,
    required :: HashSet SomeDepRep,
    depToDep :: Graph SomeDepRep, 
    depToMonad :: Bipartite.AdjacencyMap SomeDepRep SomeMonadConstraintRep
  }

emptyCheckedEnv :: forall phases m . CheckedEnv phases m
emptyCheckedEnv = CheckedEnv (DepGraph mempty mempty empty Bipartite.empty) mempty

monadConstraintRep :: forall (mc :: (Type -> Type) -> Constraint) . R.Typeable mc => SomeMonadConstraintRep
monadConstraintRep = SomeMonadConstraintRep (R.typeRep @mc)

-- depless/terminal dep (no constructor)
-- phaselessDep (no phases, only the constructor)
--
