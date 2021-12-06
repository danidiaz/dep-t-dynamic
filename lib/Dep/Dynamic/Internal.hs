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

newtype DynamicEnv (h :: Type -> Type) (m :: Type -> Type)
  = DynamicEnv (HashMap SomeDepRep Dynamic)

-- | In '(<>)', the entry for the left map is kept.
deriving newtype instance Semigroup (DynamicEnv h m)
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
data DepNotFound = DepNotFound TypeRep deriving (Show)

instance Exception DepNotFound

-- | In 'liftH2', mismatches in key sets are resolved by working with their
-- intersection, like the @Apply@ instance for @Data.Map@ in the
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

data SomeDepRep where
    SomeDepRep :: forall (a :: (Type -> Type) -> Type) . !(R.TypeRep a) -> SomeDepRep

instance Eq SomeDepRep where
    SomeDepRep r1 == SomeDepRep r2 = R.SomeTypeRep r1 == R.SomeTypeRep r2

instance Ord SomeDepRep where
    SomeDepRep r1 `compare` SomeDepRep r2 = R.SomeTypeRep r1 `compare` R.SomeTypeRep r2

instance Hashable SomeDepRep where
    hashWithSalt salt (SomeDepRep tr) = hashWithSalt salt tr
    hash (SomeDepRep tr) = hash tr 


