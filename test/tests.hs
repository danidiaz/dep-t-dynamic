{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE TupleSections #-}

module Main (main) where

import Dep.Has
import Dep.Env
import Dep.Dynamic
import Control.Monad.Dep.Class
import Control.Monad.Reader
import Data.Functor.Constant
import Data.Functor.Compose
import Data.Coerce
import Data.Kind
import Data.List (intercalate)
import GHC.Generics (Generic)
import Test.Tasty
import Test.Tasty.HUnit
import Prelude hiding (log)
import Data.Functor.Identity
import GHC.TypeLits
import Control.Monad.Trans.Cont
import Data.Aeson
import Data.Aeson.Types
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.IORef
import System.IO
import Control.Exception
import Control.Arrow (Kleisli (..))
import Data.Text qualified as Text
import Data.Function ((&))
import Data.Functor ((<&>), ($>))
import Data.String
import Data.Typeable

type Logger :: (Type -> Type) -> Type
newtype Logger d = Logger {
    info :: String -> d ()
  }

data Repository d = Repository
  { findById :: Int -> d (Maybe String)
  , putById :: Int -> String -> d ()
  , insert :: String -> d Int
  }

data Controller d = Controller 
  { create :: d Int
  , append :: Int -> String -> d Bool 
  , inspect :: Int -> d (Maybe String)
  } 

type MessagePrefix = Text.Text

data LoggerConfiguration = LoggerConfiguration { 
        messagePrefix :: MessagePrefix
    } deriving stock (Show, Generic)
      deriving anyclass FromJSON

makeStdoutLogger :: MonadIO m => MessagePrefix -> env -> Logger m
makeStdoutLogger prefix _ = Logger (\msg -> liftIO (putStrLn (Text.unpack prefix ++ msg)))

allocateMap :: ContT () IO (IORef (Map Int String))
allocateMap = ContT $ bracket (newIORef Map.empty) pure

makeInMemoryRepository 
    :: Has Logger IO env 
    => IORef (Map Int String) 
    -> env 
    -> Repository IO
makeInMemoryRepository ref (asCall -> call) = do
    Repository {
         findById = \key -> do
            call info "I'm going to do a lookup in the map!"
            theMap <- readIORef ref
            pure (Map.lookup key theMap)
       , putById = \key content -> do
            theMap <- readIORef ref
            writeIORef ref $ Map.insert key content theMap 
       , insert = \content -> do 
            call info "I'm going to insert in the map!"
            theMap <- readIORef ref
            let next = Map.size theMap
            writeIORef ref $ Map.insert next content theMap 
            pure next
    }

makeController :: (Has Logger m env, Has Repository m env, Monad m) => env -> Controller m
makeController (asCall -> call) = Controller {
      create = do
          call info "Creating a new empty resource."
          key <- call insert ""
          pure key
    , append = \key extra -> do
          call info "Appending to a resource"
          mresource <- call findById key
          case mresource of
            Nothing -> do
                pure False
            Just resource -> do
                call putById key (resource ++ extra) 
                pure True
    , inspect = \key -> do
          call findById key 
    }

-- from Has-using to positional
makeControllerPositional :: Monad m => Logger m -> Repository m -> Controller m
makeControllerPositional a b = makeController $ addDep a $ addDep b $ emptyEnv

-- from positional to Has-using
makeController' :: (Has Logger m env, Has Repository m env, Monad m) => env -> Controller m
makeController' env = makeControllerPositional (dep env) (dep env)

-- from purely Has-using to MonadDep-using
-- but this is very verbose. See 'component' in "Control.Monad.Dep.Advice" of package dep-t-advice
-- for an alternative.
makeController'' :: MonadDep [Has Logger, Has Repository] d e m => Controller m
makeController'' = Controller {
        create = useEnv \env -> create (makeController env)
      , append = \a b -> useEnv \env -> append (makeController env) a b 
      , inspect = \a -> useEnv \env -> inspect (makeController env) a  
    }

--
-- type EnvHKD :: (Type -> Type) -> (Type -> Type) -> Type
-- data EnvHKD h m = EnvHKD
--   { logger :: h (Logger m),
--     repository :: h (Repository m),
--     controller :: h (Controller m)
--   } deriving stock Generic
--     deriving anyclass (Phased, DemotableFieldNames, FieldsFindableByType)
-- 
-- deriving via Autowired (EnvHKD Identity m) instance Autowireable r_ m (EnvHKD Identity m) => Has r_ m (EnvHKD Identity m)

type Field = (,) String

type Configurator = Kleisli Parser Value 

parseConf :: FromJSON a => Configurator a
parseConf = Kleisli parseJSON

type Allocator = ContT () IO

type Phases env = Field `Compose` Configurator `Compose` Allocator `Compose` Constructor env

env :: DynamicEnv (Phases (DynamicEnv Identity IO)) IO
env =
      insertDep @Logger (fromBare $
        ("logger",) $
        parseConf <&> \(LoggerConfiguration {messagePrefix}) -> 
        pure @Allocator $
        makeStdoutLogger messagePrefix)
    $ insertDep @Repository (fromBare $ 
        ("repository",) $
        pure @Configurator $
        allocateMap <&> \ref -> 
        makeInMemoryRepository ref)
    $ insertDep @Controller (fromBare $ 
        ("controller",) $ 
        pure @Configurator $
        pure @Allocator $ 
        makeController)
    $ mempty

env' :: Kleisli Parser Object (DynamicEnv (Allocator `Compose` Constructor (DynamicEnv Identity IO)) IO)
env' = traverseH trans env
    where 
    trans (Compose (fieldName, Compose (Kleisli f))) =
        Kleisli \o -> explicitParseField f o (fromString fieldName) 

testEnvConstruction :: Assertion
testEnvConstruction = do
    let parseResult = eitherDecode' (fromString "{ \"logger\" : { \"messagePrefix\" : \"[foo]\" }, \"repository\" : null, \"controller\" : null }")
    print parseResult 
    let Right value = parseResult 
        Kleisli (withObject "configuration" -> parser) = env'
        Right allocators = parseEither parser value 
    runContT (pullPhase @Allocator allocators) \constructors -> do
        let (asCall -> call) = fixEnv constructors
        resourceId <- call create
        call append resourceId "foo"
        call append resourceId "bar"
        Just result <- call inspect resourceId
        assertEqual "" "foobar" $ result


envMissing :: DynamicEnv (Phases (DynamicEnv Identity IO)) IO
envMissing =
      insertDep (
        ("repository",()) `bindPhase` \() ->  
        skipPhase @Configurator $
        allocateMap `bindPhase` \ref -> 
        constructor (makeInMemoryRepository ref)
      )
    $ insertDep (
        ("controller",()) `bindPhase` \() ->  
        skipPhase @Configurator $
        skipPhase @Allocator $ 
        constructor makeController
      )
    $ mempty


envMissing' :: Kleisli Parser Object (DynamicEnv (Allocator `Compose` Constructor (DynamicEnv Identity IO)) IO)
envMissing' = traverseH trans envMissing
    where 
    trans (Compose (fieldName, Compose (Kleisli f))) =
        Kleisli \o -> explicitParseField f o (fromString fieldName) 


testMissingDep :: Assertion
testMissingDep = do
    let parseResult = eitherDecode' (fromString "{ \"logger\" : { \"messagePrefix\" : \"[foo]\" }, \"repository\" : null, \"controller\" : null }")
    print parseResult 
    let Right value = parseResult 
        Kleisli (withObject "configuration" -> parser) = envMissing'
        Right allocators = parseEither parser value 
    runContT (pullPhase @Allocator allocators) \constructors -> do
        let (asCall -> call) = fixEnv constructors
        e <- tryJust (fromException @DepNotFound) (call create)
        case e of
            Left (DepNotFound x) | x == typeRep (Proxy @(Logger IO)) -> pure ()
            _ -> assertFailure "exception expected"


--
--
--
tests :: TestTree
tests =
  testGroup
    "All"
    [
        testCase "environmentConstruction" testEnvConstruction
    ,   testCase "missing" testMissingDep
    ]

main :: IO ()
main = defaultMain tests
