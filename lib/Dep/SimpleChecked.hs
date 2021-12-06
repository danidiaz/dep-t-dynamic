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

module Dep.SimpleChecked where

import Data.Coerce
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
import qualified Algebra.Graph
import Algebra.Graph.AdjacencyMap (AdjacencyMap)
import qualified Algebra.Graph.Bipartite.Undirected.AdjacencyMap as Bipartite

data CheckedEnv phases m = CheckedEnv (DynamicEnv (phases `Compose` Constructor (DynamicEnv Identity m)) m)

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
checkedDep f (CheckedEnv de) =
  let demoteDep :: forall (x :: (Type -> Type) -> Type). R.Typeable x => K SomeDepRep x
      demoteDep = K (SomeDepRep (R.typeRep @x))
      depReps = collapse_NP $ cpure_NP @R.Typeable @rs Proxy demoteDep
      demoteMonadCapability :: forall (x :: (Type -> Type) -> Constraint). R.Typeable x => K SomeMonadConstraintRep x
      demoteMonadCapability = K (SomeMonadConstraintRep (R.typeRep @x))
      monadCapabilityReps = collapse_NP $ cpure_NP @R.Typeable @mcs Proxy demoteMonadCapability
   in CheckedEnv (insertDep (f @(DynamicEnv Identity m) @m) de)

type Bare :: Type -> Type
type family Bare x where
  Bare (Compose outer inner x) = Bare (outer (Bare (inner x)))
  Bare other = other

toBare :: Coercible phases (Bare phases) => phases -> Bare phases
toBare = coerce

fromBare :: Coercible phases (Bare phases) => Bare phases -> phases
fromBare = coerce

data SomeMonadConstraintRep where
  SomeMonadConstraintRep :: forall (a :: (Type -> Type) -> Constraint). !(R.TypeRep a) -> SomeMonadConstraintRep

instance Eq SomeMonadConstraintRep where
    SomeMonadConstraintRep r1 == SomeMonadConstraintRep r2 = R.SomeTypeRep r1 == R.SomeTypeRep r2

instance Ord SomeMonadConstraintRep where
    SomeMonadConstraintRep r1 `compare` SomeMonadConstraintRep r2 = R.SomeTypeRep r1 `compare` R.SomeTypeRep r2

instance Hashable SomeMonadConstraintRep where
  hashWithSalt salt (SomeMonadConstraintRep tr) = hashWithSalt salt tr
  hash (SomeMonadConstraintRep tr) = hash tr

data Deps = Deps
  { provided :: HashSet SomeDepRep,
    required :: HashSet SomeDepRep,
    depGraph :: AdjacencyMap SomeDepRep
  }

data RequiredMonadConstraints = RequiredMonadConstraints (Bipartite.AdjacencyMap SomeDepRep SomeMonadConstraintRep)

-- depless/terminal dep (no constructor)
-- phaselessDep (no phases, only the constructor)
--
