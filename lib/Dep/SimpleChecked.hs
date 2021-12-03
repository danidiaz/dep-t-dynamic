{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Dep.SimpleChecked  where

import Data.Functor.Compose
import Data.Kind
import Data.SOP (K (..))
import Data.SOP qualified as SOP
import Data.SOP.NP 
import Data.Typeable
import Dep.Dynamic
import Dep.Env
import GHC.TypeLits
import Data.Coerce

data CheckedEnv phases m = CheckedEnv (DynamicEnv (phases `Compose` Constructor (DynamicEnv Identity m)) m)

type HasAll :: [(Type -> Type) -> Type] -> (Type -> Type) -> Type -> Constraint
type family HasAll rs m e where
  HasAll '[] m e = ()
  HasAll (r_ : rs) m e = (Has r_ m e, HasAll rs m e)

type MonadSatisfiesAll :: [(Type -> Type) -> Constraint] -> (Type -> Type) -> Constraint
type family MonadSatisfiesAll cs m where
  MonadSatisfiesAll '[] m = ()
  MonadSatisfiesAll (c : cs) m = (c m, MonadSatisfiesAll cs m)

checkedDep ::
  forall rs mcs r_ m phases.
  ( SOP.All Typeable rs,
    SOP.All Typeable mcs,
    Typeable r_,
    Typeable m,
    Typeable phases,
    HasAll rs m (DynamicEnv Identity m),
    MonadSatisfiesAll mcs m
  ) =>
  -- | stuff
  ( forall e n.
    ( HasAll rs n e,
      MonadSatisfiesAll mcs n
    ) =>
    (phases `Compose` Constructor e) (r_ n)
  ) ->
  -- | stuff
  CheckedEnv phases m ->
  CheckedEnv phases m
checkedDep f (CheckedEnv de) = 
    let demote :: forall x . Typeable x => K TypeRep x
        demote = K (typeRep (Proxy @x))
        depReps = collapse_NP $ cpure_NP @Typeable @rs Proxy demote
        monadConstraintReps = collapse_NP $ cpure_NP @Typeable @mcs Proxy demote
     in CheckedEnv (insertDep (f @(DynamicEnv Identity m) @m) de)

type Bare :: Type -> Type
type family Bare x where
    Bare (Compose outer inner x) = Bare (outer (Bare (inner x)))
    Bare other = other

fromBare :: Coercible phases (Bare phases) => Bare phases -> phases
fromBare = coerce

-- depless/terminal dep (no constructor)
-- phaselessDep (no phases, only the constructor) 
--
