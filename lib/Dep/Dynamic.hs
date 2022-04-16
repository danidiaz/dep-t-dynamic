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

-- | This module provies a dynamic version of a dependency injection
-- environment.
--
-- You don't need to declare beforehand what fields exist in the environment,
-- you can simply add them using 'insertDep'.
--
-- I might be useful for quick prototyping, or for when there is a big number
-- of components and putting all of them in a conventional record would slow
-- compilation.
--
-- A 'Dep.Env.fixEnv'-based example:
--
-- >>> :{
--  newtype Foo d = Foo {foo :: String -> d ()} deriving Generic
--  newtype Bar d = Bar {bar :: String -> d ()} deriving Generic
--  makeIOFoo :: MonadIO m => Foo m
--  makeIOFoo = Foo (liftIO . putStrLn)
--  makeBar :: Has Foo m env => env -> Bar m
--  makeBar (asCall -> call) = Bar (call foo)
--  env :: DynamicEnv (Constructor (DynamicEnv Identity IO)) IO
--  env = mempty 
--      & insertDep @Foo (constructor (\_ -> makeIOFoo))
--      & insertDep @Bar (constructor makeBar) 
--  envReady :: DynamicEnv Identity IO
--  envReady = fixEnv env
-- :}
--
-- >>> :{
--  bar (dep envReady) "this is bar"
-- :}
-- this is bar
--
-- The same example using 'Control.Monad.Dep.DepT' and 'Dep.Advice.component':
--
-- >>> :{
--  env' :: DynamicEnv Identity (DepT (DynamicEnv Identity) IO)
--  env' = mempty 
--       & insertDep @Foo (Identity (component (\_ -> makeIOFoo)))
--       & insertDep @Bar (Identity (component makeBar))
-- :}
--
-- >>> :{
--  runFromDep (pure env') bar "this is bar"
-- :}
-- this is bar
--
-- Components are found by type. Use "Dep.Tagged" to disambiguate components of
-- the same type.
--
-- It's not checked at compilation time that the dependencies for all
-- components in the environment are also present in the environment. A
-- `DynamicEnv` exception will be thrown at run time whenever a component tries to
-- find a dependency that doesn't exist: 
--
-- >>> :{
--  badEnv :: DynamicEnv Identity IO
--  badEnv = mempty
-- :}
--
-- >>> :{
--  bar (dep badEnv) "this is bar"
-- :}
-- *** Exception: DepNotFound (Bar IO)
--
-- See `Dep.Checked` and `Dep.SimpleChecked` for safer (but still dynamically typed) approaches.
--
-- See also `Dep.Env.InductiveEnv` for a strongly-typed variant.
module Dep.Dynamic
  (
  -- * A dynamic environment
    DynamicEnv
  , insertDep
  , deleteDep
  , DepNotFound (..)
  , SomeDepRep (..)
  , depRep
  -- * Re-exports
  , mempty
  , Bare
  , fromBare
  , toBare
  )
where

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
import Data.Dynamic
import Data.Type.Equality (type (==))
import Data.Typeable
import GHC.Generics qualified as G
import GHC.Records
import GHC.TypeLits
import Type.Reflection qualified as R
import Data.Hashable
import Algebra.Graph 
import Dep.Dynamic.Internal
import Data.Monoid

-- | A dependency injection environment for components with effects in the monad @m@.
--
-- The components are wrapped in an 'Applicative' phase @h@, which will be
-- 'Data.Functor.Identity.Identity' for \"ready-to-be-used\" environments.
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
-- >>> :set -XTypeOperators
-- >>> import Data.Kind
-- >>> import Control.Monad.Dep
-- >>> import Data.Function
-- >>> import GHC.Generics (Generic)
-- >>> import Dep.Has
-- >>> import Dep.Env
-- >>> import Dep.Dynamic
-- >>> import Dep.Advice (component, runFromDep)

