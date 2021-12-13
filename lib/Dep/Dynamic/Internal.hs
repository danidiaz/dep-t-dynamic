{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Dep.Dynamic.Internal where

import Dep.Env
import Dep.Has
import Control.Applicative
import Control.Exception
import Data.Coerce
import Data.Function (fix)
import Data.Functor (($>), (<&>))
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Functor.Compose
import Data.Functor.Constant
import Data.Functor.Identity
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as H
import Data.Kind
import Data.Proxy
import Data.String
import Data.Type.Equality (type (==))
import Data.Typeable
import GHC.Generics qualified as G
import GHC.Records
import GHC.TypeLits
import Type.Reflection qualified as R
import Data.Hashable
import Algebra.Graph 
import qualified Algebra.Graph.Bipartite.Undirected.AdjacencyMap as Bipartite


-- | The type rep of a constraint over a monad. Similar to 'Type.Reflection.SomeTypeRep' 
-- but for types of a more specific kind.
data SomeMonadConstraintRep where
  SomeMonadConstraintRep :: forall (a :: (Type -> Type) -> Constraint). !(R.TypeRep a) -> SomeMonadConstraintRep

instance Eq SomeMonadConstraintRep where
    SomeMonadConstraintRep r1 == SomeMonadConstraintRep r2 = R.SomeTypeRep r1 == R.SomeTypeRep r2

instance Ord SomeMonadConstraintRep where
    SomeMonadConstraintRep r1 `compare` SomeMonadConstraintRep r2 = R.SomeTypeRep r1 `compare` R.SomeTypeRep r2

instance Hashable SomeMonadConstraintRep where
  hashWithSalt salt (SomeMonadConstraintRep tr) = hashWithSalt salt tr
  hash (SomeMonadConstraintRep tr) = hash tr

instance Show SomeMonadConstraintRep where
    show (SomeMonadConstraintRep r1) = show r1

-- | Produce a 'SomeMonadConstraintRep' by means of a type application.
monadConstraintRep :: forall (mc :: (Type -> Type) -> Constraint) . R.Typeable mc => SomeMonadConstraintRep
monadConstraintRep = SomeMonadConstraintRep (R.typeRep @mc)

-- | This type family clears newtypes like 'Compose', 'Identity' and 'Constant' from a composite type,
-- leaving you with a newtypeless nested type as result.
--
-- The idea is that it might be easier to construct values of the \"bare\" version of a composite type,
-- and later coerce them to the newtyped version using 'fromBare'.
--
-- This is mainly intended for defining the nested 'Applicative' \"phases\" of components that live in a 'Phased'
-- environment.
type Bare :: Type -> Type
type family Bare x where
  Bare (Compose outer inner x) = Bare (outer (Bare (inner x)))
  Bare (Identity x) = Bare x
  Bare (Const x k) = Bare x
  Bare (Constant x k) = Bare x
  Bare other = other

-- | Convert a value from its bare version to the newtyped one, usually as a step
-- towards inserting it into a 'Phased' environment.
fromBare :: Coercible phases (Bare phases) => Bare phases -> phases
fromBare = coerce

-- | Convert from the newtyped value to the bare one. 'fromBare' tends to be more useful.
toBare :: Coercible phases (Bare phases) => phases -> Bare phases
toBare = coerce

type MonadSatisfiesAll :: [(Type -> Type) -> Constraint] -> (Type -> Type) -> Constraint
type family MonadSatisfiesAll cs m where
  MonadSatisfiesAll '[] m = ()
  MonadSatisfiesAll (c : cs) m = (c m, MonadSatisfiesAll cs m)

-- | The type rep of a parameterizable record type. Similar to 'Type.Reflection.SomeTypeRep' 
-- but for types of a more specific kind.
data SomeDepRep where
    SomeDepRep :: forall (a :: (Type -> Type) -> Type) . !(R.TypeRep a) -> SomeDepRep

instance Eq SomeDepRep where
    SomeDepRep r1 == SomeDepRep r2 = R.SomeTypeRep r1 == R.SomeTypeRep r2

instance Ord SomeDepRep where
    SomeDepRep r1 `compare` SomeDepRep r2 = R.SomeTypeRep r1 `compare` R.SomeTypeRep r2

instance Hashable SomeDepRep where
    hashWithSalt salt (SomeDepRep tr) = hashWithSalt salt tr
    hash (SomeDepRep tr) = hash tr 

instance Show SomeDepRep where
    show (SomeDepRep r1) = show r1

-- | Produce a 'SomeDepRep' by means of a type application.
depRep :: forall (r_ :: (Type -> Type) -> Type) . R.Typeable r_ => SomeDepRep
depRep = SomeDepRep (R.typeRep @r_)




-- | A summary graph of dependencies.  
-- If the required dependencies are not a subset of the provided ones, the environment is not yet complete.
--
-- The graph datatypes come from the @algebraic-graphs@ package.
data DepGraph = DepGraph
  { provided :: HashSet SomeDepRep, -- ^ components that have been inserted in the environment
    required :: HashSet SomeDepRep, -- ^ components that are required by other components in the environment
    depToDep :: Graph SomeDepRep, -- ^ graph with dependencies components have on other components
    depToMonad :: Bipartite.AdjacencyMap SomeDepRep SomeMonadConstraintRep -- ^ bipartite graph with the constraints components require from the effect monad
  }

instance Semigroup DepGraph where 
  DepGraph {provided = provided1, required = required1, depToDep = depToDep1, depToMonad = depToMonad1}
   <> DepGraph {provided = provided2, required = required2, depToDep = depToDep2, depToMonad = depToMonad2} =
     DepGraph { provided = provided1 <> provided2
      , required = required1 <> required2
      , depToDep = overlay depToDep1 depToDep2
      , depToMonad = Bipartite.overlay depToMonad1 depToMonad2
     }

instance Monoid DepGraph where
  mempty = DepGraph mempty mempty Algebra.Graph.empty Bipartite.empty


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
-- >>> import Dep.Advice (component, runFromDep)