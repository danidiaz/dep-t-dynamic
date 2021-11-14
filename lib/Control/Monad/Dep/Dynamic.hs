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

-- | This module
module Control.Monad.Dep.Dynamic
  (
  )
where

import Control.Applicative
import Control.Exception
import Control.Monad.Dep.Env
import Control.Monad.Dep.Has
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

data DynamicEnv (h :: Type -> Type) (m :: Type -> Type)
  = DynamicEnv (HashMap TypeRep Dynamic)

emptyEnv :: forall h m. DynamicEnv h m
emptyEnv = DynamicEnv H.empty

addDep ::
  forall r_ h m.
  (Typeable r_, Typeable h, Typeable m) =>
  h (r_ m) ->
  DynamicEnv h m ->
  DynamicEnv h m
addDep component (DynamicEnv dict) =
  let key = typeRep (Proxy @r_)
   in DynamicEnv (H.insert key (toDyn component) dict)

instance (Typeable r_, Typeable m) => Has r_ m (DynamicEnv Identity m) where
  dep (DynamicEnv dict) =
    case H.lookup (typeRep (Proxy @r_)) dict of
      Nothing ->
        throw (DepNotFound (typeRep (Proxy @(r_ m))))
      Just (d :: Dynamic) ->
        case fromDynamic @(r_ m) d of
          Nothing -> error "Impossible failure converting dep."
          Just component -> component

data DepNotFound = DepNotFound TypeRep deriving (Show)

instance Exception DepNotFound


