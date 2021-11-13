{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}

module Main (main) where

import Control.Monad.Dep
import Control.Monad.Dep.Has
import Control.Monad.Dep.Env
import Control.Monad.Dep.Dynamic
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Kind
import Data.Coerce
import Data.List (intercalate)
import Test.Tasty
import Test.Tasty.HUnit
import Prelude hiding (log)

--
--
--
tests :: TestTree
tests =
  testGroup
    "All"
    [
    ]

main :: IO ()
main = defaultMain tests
