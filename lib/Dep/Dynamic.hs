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

-- | This module
module Dep.Dynamic
  (
    DynamicEnv
  , insertDep
  , DepNotFound (..)
  -- * Re-exports
  , mempty
  )
where

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
  = DynamicEnv (HashMap SomeComponentRep Dynamic)
  deriving newtype (Semigroup, Monoid)

insertDep ::
  forall r_ h m.
  (Typeable r_, Typeable h, Typeable m) =>
  h (r_ m) ->
  DynamicEnv h m ->
  DynamicEnv h m
insertDep component (DynamicEnv dict) =
  let key = SomeComponentRep (R.typeRep @r_)
   in DynamicEnv (H.insert key (toDyn component) dict)

instance (Typeable r_, Typeable m) => Has r_ m (DynamicEnv Identity m) where
  dep (DynamicEnv dict) =
    case H.lookup (SomeComponentRep (R.typeRep @r_)) dict of
      Nothing ->
        throw (DepNotFound (typeRep (Proxy @(r_ m))))
      Just (d :: Dynamic) ->
        case fromDynamic @(Identity (r_ m)) d of
          Nothing -> error "Impossible failure converting dep."
          Just (Identity component) -> component

data DepNotFound = DepNotFound TypeRep deriving (Show)

instance Exception DepNotFound

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
        SomeComponentRep tr -> 
            R.withTypeable tr (withComponent tr d)

    --    => (forall x . h x -> f (g x)) -> env_ h m -> f (env_ g m)
    liftA2H
        :: forall (a :: Type -> Type) (f :: Type -> Type) (f' :: Type -> Type) (m :: Type -> Type) .
        ( Typeable a
        , Typeable f
        , Typeable f'
        , Typeable m
        )
        -- | 
        => (forall x. a x -> f x -> f' x) 
        -- |
        -> DynamicEnv a m 
        -- |
        -> DynamicEnv f m 
        -- |
        -> DynamicEnv f' m
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
        SomeComponentRep tr -> 
            R.withTypeable tr (withComponent tr dpair)

data SomeComponentRep where
    SomeComponentRep :: forall (a :: (Type -> Type) -> Type) . !(R.TypeRep a) -> SomeComponentRep

instance Eq SomeComponentRep where
    SomeComponentRep r1 == SomeComponentRep r2 = 
        case r1 `R.eqTypeRep` r2 of
          Just _  -> True
          Nothing -> False

instance Hashable SomeComponentRep where
    hashWithSalt salt (SomeComponentRep tr) = hashWithSalt salt tr
    hash (SomeComponentRep tr) = hash tr 

