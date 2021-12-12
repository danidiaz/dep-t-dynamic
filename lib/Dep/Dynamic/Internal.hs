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
import Data.Dynamic
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

newtype DynamicEnv (h :: Type -> Type) (m :: Type -> Type)
  = DynamicEnv (HashMap SomeDepRep Dynamic)

-- | In '(<>)', the entry for the left map is kept.
deriving newtype instance Semigroup (DynamicEnv h m)

-- | 'mempty' is for creating the empty environment.
deriving newtype instance Monoid (DynamicEnv h m)

-- | Insert a record component wrapped in the environment's phase parameter @h@.
insertDep ::
  forall r_ h m.
  (Typeable r_, Typeable h, Typeable m) =>
  h (r_ m) ->
  DynamicEnv h m ->
  DynamicEnv h m
insertDep component (DynamicEnv dict) =
  let key = SomeDepRep (R.typeRep @r_)
   in DynamicEnv (H.insert key (toDyn component) dict)

-- | The record type to delete is supplied through a type application.
deleteDep ::
  forall (r_ :: (Type -> Type) -> Type) h m.
  Typeable r_ =>
  DynamicEnv h m ->
  DynamicEnv h m
deleteDep (DynamicEnv dict) =
  let key = SomeDepRep (R.typeRep @r_)
   in DynamicEnv (H.delete key dict)

-- | 'DynamicEnv' has a 'Data.Has.Has' instance for every possible component. If the
-- component is not actually in the environment, 'DepNotFound' is thrown.
instance (Typeable r_, Typeable m) => Has r_ m (DynamicEnv Identity m) where
  dep (DynamicEnv dict) =
    case H.lookup (SomeDepRep (R.typeRep @r_)) dict of
      Nothing ->
        throw (DepNotFound (typeRep (Proxy @(r_ m))))
      Just (d :: Dynamic) ->
        case fromDynamic @(Identity (r_ m)) d of
          Nothing -> error "Impossible failure converting dep."
          Just (Identity component) -> component

-- | Exception thrown by 'dep' when the component we are looking for is not
-- present in the environment.
newtype DepNotFound = DepNotFound TypeRep deriving (Show)

instance Exception DepNotFound

-- | In 'liftH2', mismatches in key sets are resolved by working with their
-- intersection, like how the @Apply@ instance for @Data.Map@ in the
-- \"semigroupoids\" package works.
instance Phased DynamicEnv where
    traverseH 
        :: forall (h :: Type -> Type) (f :: Type -> Type) (g :: Type -> Type) (m :: Type -> Type). 
        ( Applicative f 
        , Typeable f
        , Typeable g
        , Typeable h
        , Typeable m
        )
        => (forall x . h x -> f (g x)) 
        -> DynamicEnv h m 
        -> f (DynamicEnv g m)
    traverseH trans (DynamicEnv dict) = DynamicEnv <$> H.traverseWithKey dynTrans dict
      where
      withComponent :: forall (r_ :: (Type -> Type) -> Type) .  Typeable r_
                    => R.TypeRep r_ 
                    -> Dynamic
                    -> f Dynamic
      withComponent _ d = 
        case fromDynamic @(h (r_ m)) d of
          Nothing -> error "Impossible failure converting dep."
          Just hcomponent -> toDyn <$> trans hcomponent
      dynTrans k d = case k of
        SomeDepRep tr -> 
            R.withTypeable tr (withComponent tr d)

    liftA2H
        :: forall (a :: Type -> Type) (f :: Type -> Type) (f' :: Type -> Type) (m :: Type -> Type) .
        ( Typeable a
        , Typeable f
        , Typeable f'
        , Typeable m
        ) =>
        (forall x. a x -> f x -> f' x) ->
        -- |
        DynamicEnv a m ->
        -- |
        DynamicEnv f m ->
        -- |
        DynamicEnv f' m
    liftA2H trans (DynamicEnv dicta) (DynamicEnv dictb) = DynamicEnv (H.mapWithKey dynTrans (H.intersectionWith (,) dicta dictb))
      where
      withComponent :: forall (r_ :: (Type -> Type) -> Type) . Typeable r_
                    => R.TypeRep r_ 
                    -> (Dynamic, Dynamic)
                    -> Dynamic
      withComponent _ (da, df)  = 
        case (fromDynamic @(a (r_ m)) da, fromDynamic @(f (r_ m)) df) of
          (Nothing, _) -> error "Impossible failure converting left dep."
          (_, Nothing) -> error "Impossible failure converting right dep."
          (Just acomponent, Just fcomponent) -> toDyn (trans acomponent fcomponent)
      dynTrans k dpair = case k of
        SomeDepRep tr -> 
            R.withTypeable tr (withComponent tr dpair)

-- | The type rep of a parameterizable record type. Similar to 'Type.Reflection.SomeTypeRep' 
-- but for values of a more specific kind.
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

depRep :: forall (r_ :: (Type -> Type) -> Type) . R.Typeable r_ => SomeDepRep
depRep = SomeDepRep (R.typeRep @r_)

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

data DepGraph = DepGraph
  { provided :: HashSet SomeDepRep,
    required :: HashSet SomeDepRep,
    depToDep :: Graph SomeDepRep, 
    depToMonad :: Bipartite.AdjacencyMap SomeDepRep SomeMonadConstraintRep
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