{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Dep.Checked where

import Control.Monad.Dep
import Data.Functor.Compose
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Hashable
import Data.Kind
import Data.Proxy
import Data.SOP (K (..))
import Data.SOP qualified as SOP
import Data.SOP.NP
import Dep.Dynamic
import Dep.Dynamic.Internal
import Dep.Env
import GHC.TypeLits
import Type.Reflection qualified as R
import Data.Functor
import Algebra.Graph 
import qualified Algebra.Graph.Bipartite.Undirected.AdjacencyMap as Bipartite

data CheckedEnv phases re_ m = CheckedEnv DepGraph (DynamicEnv phases (DepT (re_ (DynamicEnv Identity)) m))

checkedDep ::
  forall rs mcs r_ phases re_ m.
  ( SOP.All R.Typeable rs,
    SOP.All R.Typeable mcs,
    R.Typeable r_,
    R.Typeable re_,
    R.Typeable m,
    R.Typeable phases,
    HasAll rs m (re_ (DynamicEnv Identity) (DepT (re_ (DynamicEnv Identity)) m)),
    MonadSatisfiesAll mcs (DepT (re_ (DynamicEnv Identity)) m)
  ) =>
  -- | stuff
  ( forall e_ n.
    ( HasAll rs n (e_ (DepT e_ n)),
      MonadSatisfiesAll mcs (DepT e_ n)
    ) =>
    phases (r_ (DepT e_ n))
  ) ->
  -- | stuff
  CheckedEnv phases re_ m ->
  CheckedEnv phases re_ m
checkedDep f (CheckedEnv DepGraph {provided,required,depToDep,depToMonad} de) =
  let demoteDep :: forall (x :: (Type -> Type) -> Type). R.Typeable x => K SomeDepRep x
      demoteDep = K (depRep @x)
      depReps = collapse_NP $ cpure_NP @R.Typeable @rs Proxy demoteDep
      demoteMonadConstraint :: forall (x :: (Type -> Type) -> Constraint). R.Typeable x => K SomeMonadConstraintRep x
      demoteMonadConstraint = K (SomeMonadConstraintRep (R.typeRep @x))
      monadConstraintReps = collapse_NP $ cpure_NP @R.Typeable @mcs Proxy demoteMonadConstraint
      provided' = HashSet.insert (depRep @r_) provided 
      required' = foldr HashSet.insert required depReps
      depGraph' = DepGraph {
            provided = provided'
        ,   required = required'
        ,   depToDep = overlay depToDep $ edges $ (depRep @r_,) <$> depReps
        ,   depToMonad = Bipartite.overlay depToMonad $ Bipartite.edges $ (depRep @r_,) <$> monadConstraintReps
        }
   in CheckedEnv depGraph' (insertDep (f @(re_ (DynamicEnv Identity))) de)

-- 
-- terminalDep ::
--   forall mcs r_ m phases.
--   ( SOP.All R.Typeable mcs,
--     R.Typeable r_,
--     R.Typeable m,
--     R.Typeable phases,
--     Functor phases,
--     MonadSatisfiesAll mcs m
--   ) =>
--   -- | stuff
--   ( forall n.
--     ( 
--       MonadSatisfiesAll mcs n
--     ) =>
--     phases (r_ n)
--   ) ->
--   -- | stuff
--   CheckedEnv phases m ->
--   CheckedEnv phases m
-- terminalDep f = checkedDep @'[] @mcs @r_ @m @phases (Compose (f <&> \c -> constructor (const c)))
-- 
-- data SomeMonadConstraintRep where
--   SomeMonadConstraintRep :: forall (a :: (Type -> Type) -> Constraint). !(R.TypeRep a) -> SomeMonadConstraintRep
-- 
-- instance Eq SomeMonadConstraintRep where
--     SomeMonadConstraintRep r1 == SomeMonadConstraintRep r2 = R.SomeTypeRep r1 == R.SomeTypeRep r2
-- 
-- instance Ord SomeMonadConstraintRep where
--     SomeMonadConstraintRep r1 `compare` SomeMonadConstraintRep r2 = R.SomeTypeRep r1 `compare` R.SomeTypeRep r2
-- 
-- instance Hashable SomeMonadConstraintRep where
--   hashWithSalt salt (SomeMonadConstraintRep tr) = hashWithSalt salt tr
--   hash (SomeMonadConstraintRep tr) = hash tr
-- 
-- instance Show SomeMonadConstraintRep where
--     show (SomeMonadConstraintRep r1) = show r1

-- emptyCheckedEnv :: forall phases m . CheckedEnv phases m
-- emptyCheckedEnv = CheckedEnv (DepGraph mempty mempty empty Bipartite.empty) mempty
-- 
-- monadConstraintRep :: forall (mc :: (Type -> Type) -> Constraint) . R.Typeable mc => SomeMonadConstraintRep
-- monadConstraintRep = SomeMonadConstraintRep (R.typeRep @mc)
-- 
-- unchecked :: CheckedEnv phases m -> (DepGraph, DynamicEnv (phases `Compose` Constructor (DynamicEnv Identity m)) m)
-- unchecked (CheckedEnv g d) = (g, d)
-- 
-- checkEnv :: CheckedEnv phases m -> Either (HashSet SomeDepRep) (DepGraph, DynamicEnv (phases `Compose` Constructor (DynamicEnv Identity m)) m)
-- checkEnv (CheckedEnv g@DepGraph {required,provided} d) = 
--   let missing = HashSet.difference required provided 
--    in if HashSet.null missing
--       then Right (g, d)
--       else Left missing
-- 
-- -- phaselessDep (no phases, only the constructor)
-- --
-- 