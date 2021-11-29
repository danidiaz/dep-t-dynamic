{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImportQualifiedPost #-}
module Dep.SimpleChecked (CheckedEnv) where

import Data.Kind
import Dep.Env
import Data.Functor.Compose
import GHC.TypeLits
import Dep.Dynamic
import Data.SOP qualified as SOP

data CheckedEnv phases m = CheckedEnv (DynamicEnv (UnderConstruction phases DynamicEnv m) m)

type UnderConstruction :: [Type -> Type] -> ((Type -> Type) -> (Type -> Type) -> Type) -> (Type -> Type) -> Type -> Type
newtype UnderConstruction phases e_ m x = UnderConstruction (ExpandPhases phases e_ m x)

type ExpandPhases :: [Type -> Type] -> ((Type -> Type) -> (Type -> Type) -> Type) -> (Type -> Type) -> Type -> Type
type family ExpandPhases phases e_ m where
    ExpandPhases '[] e_ m = Constructor e_ m
    ExpandPhases (p ': ps) e_ m  = p `Compose` ExpandPhases ps e_ m


