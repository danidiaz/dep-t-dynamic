{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}
module Dep.SimpleChecked where

import Data.Kind
import Dep.Env
import Data.Functor.Compose
import GHC.TypeLits

data CheckedEnv = CheckedEnv 

type UnfoldPhases :: ((Type -> Type) -> (Type -> Type) -> Type) -> (Type -> Type) -> [Type -> Type] -> Type -> Type
type family UnfoldPhases e_ m phases where
    UnfoldPhases e_ m '[] = Constructor e_ m
    UnfoldPhases e_ m (p ': ps) = p `Compose` UnfoldPhases e_ m ps


