{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
module Dep.SimpleChecked (CheckedEnv) where

import Data.Typeable
import Data.Kind
import Dep.Env
import Data.Functor.Compose
import GHC.TypeLits
import Dep.Dynamic
import Data.SOP qualified as SOP

data CheckedEnv phases m = CheckedEnv (DynamicEnv (UnderConstruction phases m) m)

type UnderConstruction :: [Type -> Type] -> (Type -> Type) -> Type -> Type
newtype UnderConstruction phases m x = UnderConstruction (ExpandPhases phases m x)

type ExpandPhases :: [Type -> Type] -> (Type -> Type) -> Type -> Type
type family ExpandPhases phases m where
    ExpandPhases '[] m = Constructor DynamicEnv m
    ExpandPhases (p ': ps) m  = p `Compose` ExpandPhases ps m

type HasAll :: [(Type -> Type) -> Type] -> (Type -> Type) -> Type -> Constraint
type family HasAll rs m e where
    HasAll '[] m e = ()
    HasAll (r_ : rs) m e = (Has r_ m e, HasAll rs m e)

type AllTypeable :: [k] -> Constraint
type family AllTypeable xs where
    AllTypeable '[] = ()
    AllTypeable  (x : xs) = (Typeable x, AllTypeable xs)

type MonadSatisfiesAll :: [(Type -> Type) -> Constraint] -> (Type -> Type) -> Constraint
type family MonadSatisfiesAll cs m where
    MonadSatisfiesAll '[] m = ()
    MonadSatisfiesAll (c : cs) m = (c m, MonadSatisfiesAll cs m)

checkedDep :: forall rs mcs phases r_ m . UnderConstruction phases m (r_ m) -> CheckedEnv phases m -> CheckedEnv phases m
checkedDep = undefined



