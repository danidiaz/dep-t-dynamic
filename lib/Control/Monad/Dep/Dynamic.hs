{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}

-- | This module 
module Control.Monad.Dep.Dynamic (
    ) where

import Data.Kind
import GHC.Records
import GHC.TypeLits
import Data.Coerce
import GHC.Generics qualified as G
import Control.Applicative
import Control.Monad.Dep.Has 
import Control.Monad.Dep.Env
import Data.Proxy
import Data.Functor ((<&>), ($>))
import Data.Functor.Compose
import Data.Functor.Constant
import Data.Functor.Identity
import Data.Function (fix)
import Data.String
import Data.Type.Equality (type (==))
import Data.Dynamic
import Data.Typeable
import Type.Reflection qualified as R
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as H

data DynamicEnv (h :: Type -> Type) (m :: Type -> Type) = 
    DynamicEnv (R.TypeRep h) (R.TypeRep m) (HashMap TypeRep Dynamic)

emptyDynEnv :: forall h m . (Typeable h, Typeable m) => DynamicEnv h m 
emptyDynEnv = DynamicEnv (R.typeRep @h) (R.typeRep @m) H.empty

addDynDep :: forall r_ h m . (Typeable r_, Typeable h, Typeable m) => h (r_ m) -> DynamicEnv h m -> DynamicEnv h m
addDynDep component (DynamicEnv htr mtr dict) = 
    let key = typeRep (Proxy @r_)
     in DynamicEnv htr mtr (H.insert key (toDyn component) dict)

instance (Typeable r_, Typeable m) => Has r_ m (DynamicEnv Identity m) where
    dep (DynamicEnv _ _ dict) =  
        case H.lookup (typeRep (Proxy @r_)) dict of
            Nothing -> error "oops"
            Just (d :: Dynamic) -> case fromDynamic @(r_ m) d of
                Nothing -> error "oops"
                Just component -> component




-- data InductiveEnv (rs :: [(Type -> Type) -> Type]) (h :: Type -> Type) (m :: Type -> Type) where
--     AddDep :: forall r_ m rs h . h (r_ m) -> InductiveEnv rs h m -> InductiveEnv (r_ : rs) h m
--     EmptyEnv :: forall m h . InductiveEnv '[] h m
