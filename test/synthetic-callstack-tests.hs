{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | An example of how an application can make use of the "dep-t" and
-- "dep-t-advice" packages for keeping a "synthetic" call stack that tracks the
-- invocations of monadic functions, though only of those which take part in dependency
-- injection.
--
-- We are assuming that the application follows a "record-of-functions" style.
module Main (main) where

import Control.Arrow ((>>>))
import Control.Exception
import Control.Monad.Dep (DepT)
import Control.Monad.IO.Unlift
import Control.Monad.Reader
import Control.Monad.Trans.Cont
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Constant
import Data.Functor.Identity
import Data.IORef
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Typeable
import Dep.Advice qualified as A
import Dep.Advice.Basic (MonadCallStack)
import Dep.Advice.Basic qualified as A
import Dep.Checked qualified as C
import Dep.Dynamic
import Dep.Env
  ( Autowireable,
    Autowired (..),
    Constructor,
    DemotableFieldNames,
    FieldsFindableByType,
    Phased,
    bindPhase,
    constructor,
    demoteFieldNames,
    fixEnv,
    pullPhase,
    skipPhase,
  )
import Dep.Has
  ( Has (dep),
    HasAll,
    asCall,
  )
import Dep.SimpleAdvice
  ( Advice,
    AspectT (..),
    Top,
    adviseRecord,
    advising,
    makeExecutionAdvice,
  )
import Dep.SimpleAdvice.Basic
  ( HasSyntheticCallStack (callStack),
    MethodName,
    StackFrame,
    SyntheticCallStack,
    SyntheticStackTrace,
    SyntheticStackTraceException (SyntheticStackTraceException),
    injectFailures,
    keepCallStack,
  )
import Dep.SimpleChecked qualified as SC
import Dep.Tagged (Tagged (..), tagged, untag)
import GHC.Generics (Generic)
import GHC.TypeLits
import Lens.Micro (Lens', lens)
import System.IO
import Test.Tasty
import Test.Tasty.HUnit
import Prelude hiding (insert, lookup)
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet

-- THE BUSINESS LOGIC
--
--

-- Component interfaces, defined as records polymorphic over the effect monad.
newtype Logger m = Logger
  { emitMsg :: String -> m ()
  }
  deriving stock (Generic)

data Repository m = Repository
  { insert :: Int -> m (),
    lookup :: Int -> m Bool
  }
  deriving stock (Generic)

newtype Controller m = Controller
  { -- insert one arg, look up the other. Nonsensical, but good enough for an example.
    route :: Int -> Int -> m Bool
  }
  deriving stock (Generic)

-- Component implementations, some of which depend on other components.
--
makeStdoutLogger :: MonadIO m => Logger m
makeStdoutLogger = Logger \msg -> liftIO $ putStrLn msg

-- allocation helper.
allocateSet :: Allocator (IORef (Set Int))
allocateSet = ContT $ bracket (newIORef Set.empty) pure

-- When a component depends on another, it does so by taking an "env" parameter
-- in the constructor and requiring 'Has' constraints on it.
makeInMemoryRepository ::
  (Has Logger m env, MonadIO m) =>
  IORef (Set Int) ->
  env ->
  Repository m
makeInMemoryRepository ref (asCall -> call) = do
  Repository
    { insert = \key -> do
        call emitMsg "inserting..."
        theSet <- liftIO $ readIORef ref
        liftIO $ writeIORef ref $ Set.insert key theSet,
      lookup = \key -> do
        call emitMsg "looking..."
        theSet <- liftIO $ readIORef ref
        pure (Set.member key theSet)
    }

-- This implementation of Controller depends both on the Logger and the
-- Repository.
--
-- In general, the graph of dependencies between components can be a complex
-- directed acyclic graph.
makeController ::
  (Has Logger m env, Has Repository m env, Monad m) =>
  env ->
  Controller m
makeController (asCall -> call) =
  Controller
    { route = \toInsert toLookup -> do
        call emitMsg "serving..."
        call insert toInsert
        call emitMsg "before lookup..."
        call lookup toLookup
    }

type MakeController2LoggersDeps = '[Logger, Tagged "secondary" Logger, Repository]

makeController2Loggers ::
  (HasAll MakeController2LoggersDeps m env, Monad m) =>
  env ->
  Controller m
makeController2Loggers (asCall -> call) =
  Controller
    { route = \toInsert toLookup -> do
        call (untag @"secondary" >>> emitMsg) "serving..."
        call insert toInsert
        call emitMsg "before lookup..."
        call lookup toLookup
    }

-- THE COMPOSITION ROOT
--
-- Here we define our dependency injection environment.
--
-- We put all the components which will form part of our application in an
-- environment record.
--
-- Each field is wrapped in a functor `h` which controls the "phases" we must
-- go through in  the construction of the environment. When `h` becomes
-- Identity, the environment is ready for use. (This is an example of the
-- "Higer-Kinded Data" pattern.)

-- The "phases" that components go through until fully built. Each phase
-- is represented as an applicative functor. The succession of phases is
-- defined using Data.Functor.Compose.
--
type Phases = Allocator

-- A phase in which we might allocate some resource needed by the component,
-- also set some bracket-like resource management.
-- The "managed" library could be used instead of ContT.
type Allocator = ContT () IO

-- Environment value
--
-- The base monad is a 'ReaderT' holding a SyntheticCallStack value which gets modified
-- using "local" for each sub-call.
--
-- Notice that neither the interfaces nor the implementations which we defined
-- earlier knew anything about the ReaderT.
env :: SC.CheckedEnv Phases (ReaderT SyntheticCallStack IO)
env =
  SC.checkedDep @Logger @'[] @'[MonadUnliftIO, MonadCallStack, MonadFail]
    ( fromBare $
        allocateBombs 1 <&> \bombs ->
          \_ ->
            advising
              ( adviseRecord @Top @Top \method ->
                  keepCallStack ioEx method <> injectFailures bombs
              )
              makeStdoutLogger
    )
    . SC.checkedDep @(Tagged "secondary" Logger) @'[] @'[MonadUnliftIO, MonadCallStack, MonadFail]
      ( fromBare $
          allocateBombs 0 <&> \bombs ->
            \_ ->
              advising
                ( adviseRecord @Top @Top \method ->
                    keepCallStack ioEx method <> injectFailures bombs
                )
                (tagged @"secondary" makeStdoutLogger)
      )
    . SC.checkedDep @Repository @'[Logger] @'[MonadUnliftIO, MonadCallStack, MonadFail]
      ( fromBare $
          allocateSet <&> \ref ->
            \env ->
              advising
                ( adviseRecord @Top @Top \method ->
                    keepCallStack ioEx method
                )
                (makeInMemoryRepository ref env)
      )
    . SC.checkedDep @Controller @'[Logger, Repository] @'[MonadUnliftIO, MonadCallStack, MonadFail]
      ( fromBare $
          pure @Allocator $
            \env ->
              makeController env
                & advising
                  ( adviseRecord @Top @Top \method ->
                      keepCallStack ioEx method
                  )
      )
    $ mempty


envLoggerMissing :: SC.CheckedEnv Phases (ReaderT SyntheticCallStack IO)
envLoggerMissing =
    SC.checkedDep @(Tagged "secondary" Logger) @'[] @'[MonadUnliftIO, MonadCallStack, MonadFail]
      ( fromBare $
          allocateBombs 0 <&> \bombs ->
            \_ ->
              advising
                ( adviseRecord @Top @Top \method ->
                    keepCallStack ioEx method <> injectFailures bombs
                )
                (tagged @"secondary" makeStdoutLogger)
      )
    . SC.checkedDep @Repository @'[Logger] @'[MonadUnliftIO, MonadCallStack, MonadFail]
      ( fromBare $
          allocateSet <&> \ref ->
            \env ->
              advising
                ( adviseRecord @Top @Top \method ->
                    keepCallStack ioEx method
                )
                (makeInMemoryRepository ref env)
      )
    . SC.checkedDep @Controller @'[Logger, Repository] @'[MonadUnliftIO, MonadCallStack, MonadFail]
      ( fromBare $
          pure @Allocator $
            \env ->
              makeController env
                & advising
                  ( adviseRecord @Top @Top \method ->
                      keepCallStack ioEx method
                  )
      )
    $ mempty


-- Catch only IOExceptions for this example.
ioEx :: SomeException -> Maybe IOError
ioEx = fromException @IOError

-- Allocate a supply of potentially exception-throwing actions.
allocateBombs :: Int -> Allocator (IORef ([IO ()], [IO ()]))
allocateBombs whenToBomb = ContT $ bracket (newIORef bombs) pure
  where
    bombs =
      ( replicate whenToBomb (pure ()) ++ repeat (throwIO (userError "oops")),
        repeat (pure ())
      )

-- THE COMPOSITION ROOT - ALTERNATIVE APPROACH
--
--
-- Here we'll define the dependency injection environment in a slightly
-- different way (but reusing both the "business logic" and the Env type).

-- The basic idea is that we don't perform dependency injection as a separate
-- Applicative phase (so no Constructor, but a mere Identity phase).
--
-- Instead, we shift that task into the base monad's environent.

-- As a result the "phases" are simpler:
type Phases' = Allocator `Compose` Identity

-- Now the expanded "runtime" environment will hold both the synthetic call
-- stack and the components. We define this small helper datatype for that. It
-- augments a preexisting environment with call-related info.
data CallEnv i e_ m = CallEnv
  { _callInfo :: i,
    _ops :: e_ m
  }

-- Delegate all 'Has' queries to the inner environment.
instance Has r_ m (e_ m) => Has r_ m (CallEnv i e_ m) where
  dep = dep . _ops

instance HasSyntheticCallStack (CallEnv SyntheticCallStack e_ m) where
  callStack = lens _callInfo (\(CallEnv _ ops) i' -> CallEnv i' ops)

-- Here use the DepT monad (a variant of ReaderT) as the base monad.
--
-- The environment of DepT includes-just as before-the SyntheticCallStack value
-- that is used to trace each sub-call.
--
-- But now it also includes the dependency injection context with all the
-- components.
env' :: C.CheckedEnv Phases' (CallEnv SyntheticCallStack (DynamicEnv Identity)) IO
-- env' :: Env Phases' (DepT (CallEnv SyntheticCallStack (Env Identity)) IO)
env' =
  C.checkedDep @Logger @'[] @'[MonadUnliftIO, MonadCallStack, MonadFail]
    ( fromBare $
        allocateBombs 1 <&> \bombs ->
          A.component \_ ->
              A.adviseRecord @Top @Top (\method ->
                A.keepCallStack ioEx method <> A.injectFailures bombs)
              makeStdoutLogger
    )
    . C.checkedDep @(Tagged "secondary" Logger) @'[] @'[MonadUnliftIO, MonadCallStack, MonadFail]
      ( fromBare $
          allocateBombs 0 <&> \bombs ->
            A.component \_ ->
                A.adviseRecord @Top @Top (\method ->
                  A.keepCallStack ioEx method <> A.injectFailures bombs)
                (tagged @"secondary" makeStdoutLogger)
      )
    . C.checkedDep @Repository @'[Logger] @'[MonadUnliftIO, MonadCallStack, MonadFail]
      ( fromBare $
          allocateSet <&> \ref ->
            A.component \env ->
                A.adviseRecord @Top @Top (\method ->
                  A.keepCallStack ioEx method)
                (makeInMemoryRepository ref env)
      )
    . C.checkedDep @Controller @'[Logger, Repository] @'[MonadUnliftIO, MonadCallStack, MonadFail]
      ( fromBare $
          pure @Allocator $
            A.component \env ->
              A.adviseRecord @Top @Top (\method ->
                A.keepCallStack ioEx method)
              (makeController env)
      )
  $ mempty


envLoggerMissing' :: C.CheckedEnv Phases' (CallEnv SyntheticCallStack (DynamicEnv Identity)) IO
-- env' :: Env Phases' (DepT (CallEnv SyntheticCallStack (Env Identity)) IO)
envLoggerMissing' =
    C.checkedDep @(Tagged "secondary" Logger) @'[] @'[MonadUnliftIO, MonadCallStack, MonadFail]
      ( fromBare $
          allocateBombs 0 <&> \bombs ->
            A.component \_ ->
                A.adviseRecord @Top @Top (\method ->
                  A.keepCallStack ioEx method <> A.injectFailures bombs)
                (tagged @"secondary" makeStdoutLogger)
      )
    . C.checkedDep @Repository @'[Logger] @'[MonadUnliftIO, MonadCallStack, MonadFail]
      ( fromBare $
          allocateSet <&> \ref ->
            A.component \env ->
                A.adviseRecord @Top @Top (\method ->
                  A.keepCallStack ioEx method)
                (makeInMemoryRepository ref env)
      )
    . C.checkedDep @Controller @'[Logger, Repository] @'[MonadUnliftIO, MonadCallStack, MonadFail]
      ( fromBare $
          pure @Allocator $
            A.component \env ->
              A.adviseRecord @Top @Top (\method ->
                A.keepCallStack ioEx method)
              (makeController env)
      )
  $ mempty


-- THE COMPOSITION ROOT - YET ANOTER APPROACH
--
-- This approach also uses DepT, but not to carry the dependencies, only to carry
-- the call stack (like ReaderT in the first approach).
--
-- This is done by parameterizing DepT with Constant, which makes DepT
-- behave almost as a regular ReaderT.
--
-- What are the benefits of unsing DepT instead of ReaderT here? Well, basically
-- being able to use runFinalDepT in the test, which feels somewhat cleaner than
-- runReaderT.
type RT e m = DepT (Constant e) m

env'' :: SC.CheckedEnv Phases (RT SyntheticCallStack IO)
env'' =
  SC.checkedDep @Logger @'[] @'[MonadUnliftIO, MonadCallStack, MonadFail]
    ( fromBare $
        allocateBombs 1 <&> \bombs ->
          \_ ->
            advising
              ( adviseRecord @Top @Top \method ->
                  keepCallStack ioEx method <> injectFailures bombs
              )
              makeStdoutLogger
    )
    . SC.checkedDep @(Tagged "secondary" Logger) @'[] @'[MonadUnliftIO, MonadCallStack, MonadFail]
      ( fromBare $
          allocateBombs 0 <&> \bombs ->
            \_ ->
              advising
                ( adviseRecord @Top @Top \method ->
                    keepCallStack ioEx method <> injectFailures bombs
                )
                (tagged @"secondary" makeStdoutLogger)
      )
    . SC.checkedDep @Repository @'[Logger] @'[MonadUnliftIO, MonadCallStack, MonadFail]
      ( fromBare $
          allocateSet <&> \ref ->
            \env ->
              advising
                ( adviseRecord @Top @Top \method ->
                    keepCallStack ioEx method
                )
                (makeInMemoryRepository ref env)
      )
    . SC.checkedDep @Controller @'[Logger, Repository] @'[MonadUnliftIO, MonadCallStack, MonadFail]
      ( fromBare $
          pure @Allocator $
            \env ->
              makeController env
                & advising
                  ( adviseRecord @Top @Top \method ->
                      keepCallStack ioEx method
                  )
      )
    $ mempty

-- TESTS
--
--
expectedException :: (IOError, SyntheticStackTrace)
expectedException =
  ( userError "oops",
    NonEmpty.fromList
      [ NonEmpty.fromList [(typeRep (Proxy @Logger), "emitMsg")],
        NonEmpty.fromList [(typeRep (Proxy @Repository), "insert")],
        NonEmpty.fromList [(typeRep (Proxy @Controller), "route")]
      ]
  )

expectedExceptionTagged :: (IOError, SyntheticStackTrace)
expectedExceptionTagged =
  ( userError "oops",
    NonEmpty.fromList
      [ NonEmpty.fromList
          [ (typeRep (Proxy @Logger), "emitMsg"),
            (typeRep (Proxy @(Tagged "secondary" Logger)), "unTagged")
          ],
        NonEmpty.fromList [(typeRep (Proxy @Controller), "route")]
      ]
  )

-- Test the "Constructor"-based version of the environment.
testSyntheticCallStack :: Assertion
testSyntheticCallStack = do
  let Right (_, denv) = SC.checkEnv env
      allocators = pullPhase denv
      action =
        runContT allocators \constructors -> do
          -- here we complete the construction of the environment
          let (asCall -> call) = fixEnv constructors
          flip
            runReaderT
            ([] :: SyntheticCallStack) -- the initial stack trace for the call
            ( do
                _ <- call route 1 2
                pure ()
            )
  me <- try @SyntheticStackTraceException action
  case me of
    Left (SyntheticStackTraceException (fromException @IOError -> Just ex) trace) ->
      assertEqual "exception with callstack" expectedException (ex, trace)
    Right _ -> assertFailure "expected exception did not appear"

-- Test the "Constructor"-based version of the environment.
testSyntheticCallStackTagged :: Assertion
testSyntheticCallStackTagged = do
  let Right (_, denv) = SC.checkEnv env
      denv' =
        insertDep @Controller
          ( fromBare $
              pure @Allocator $
                \env ->
                  advising
                    ( adviseRecord @Top @Top \method ->
                        keepCallStack ioEx method
                    )
                    (makeController2Loggers env)
          )
          denv
      allocators = pullPhase denv'
      action =
        runContT allocators \constructors -> do
          -- here we complete the construction of the environment
          let (asCall -> call) = fixEnv constructors
          flip
            runReaderT
            ([] :: SyntheticCallStack) -- the initial stack trace for the call
            ( do
                _ <- call route 1 2
                pure ()
            )
  me <- try @SyntheticStackTraceException action
  case me of
    Left (SyntheticStackTraceException (fromException @IOError -> Just ex) trace) ->
      assertEqual "exception with callstack" expectedExceptionTagged (ex, trace)
    Right _ -> assertFailure "expected exception did not appear"


-- Test that missing dependencies are correctly identified.
testMissingDeps :: Assertion
testMissingDeps = do
  let Left missingDeps = SC.checkEnv envLoggerMissing
   in assertEqual "Detected logger is missing" (HashSet.singleton (depRep @Logger)) missingDeps

-- Test the "DepT"-based version of the environment.
testSyntheticCallStack' :: Assertion
testSyntheticCallStack' = do
  let Right (_, denv) = C.checkEnv env'
      action =
        runContT (pullPhase @Allocator denv) \runnable -> do
          _ <- A.runFromDep (pure (CallEnv [] runnable)) route 1 2
          pure ()
  me <- try @SyntheticStackTraceException action
  case me of
    Left (SyntheticStackTraceException (fromException @IOError -> Just ex) trace) ->
      assertEqual "exception with callstack" expectedException (ex, trace)
    Right _ -> assertFailure "expected exception did not appear"

testSyntheticCallStackTagged' :: Assertion
testSyntheticCallStackTagged' = do
  let Right (_, denv) = C.checkEnv env'
      denv' =
        insertDep @Controller
          ( fromBare $
              pure @Allocator $
                A.component \env ->
                  advising
                    ( adviseRecord @Top @Top \method ->
                        keepCallStack ioEx method
                    )
                    (makeController2Loggers env)
          )
          denv
      action =
        runContT (pullPhase @Allocator denv') \runnable -> do
          _ <- A.runFromDep (pure (CallEnv [] runnable)) route 1 2
          pure ()
  me <- try @SyntheticStackTraceException action
  case me of
    Left (SyntheticStackTraceException (fromException @IOError -> Just ex) trace) ->
      assertEqual "exception with callstack" expectedExceptionTagged (ex, trace)
    Right _ -> assertFailure "expected exception did not appear"

-- Test that missing dependencies are correctly identified.
testMissingDeps' :: Assertion
testMissingDeps' = do
  let Left missingDeps = C.checkEnv envLoggerMissing'
   in assertEqual "Detected logger is missing" (HashSet.singleton (depRep @Logger)) missingDeps

testSyntheticCallStack'' :: Assertion
testSyntheticCallStack'' = do
  let Right (_, denv) = SC.checkEnv env''
      allocators = pullPhase denv
      action =
        runContT allocators \constructors -> do
          -- here we complete the construction of the environment
          let (asCall -> call) = fixEnv constructors
          A.runFinalDepT (pure (Constant [])) (call route) 1 2
          pure ()
  me <- try @SyntheticStackTraceException action
  case me of
    Left (SyntheticStackTraceException (fromException @IOError -> Just ex) trace) ->
      assertEqual "exception with callstack" expectedException (ex, trace)
    Right _ -> assertFailure "expected exception did not appear"

-- Test the "Constructor"-based version of the environment.
testSyntheticCallStackTagged'' :: Assertion
testSyntheticCallStackTagged'' = do
  let Right (_, denv) = SC.checkEnv env''
      denv' =
        insertDep @Controller
          ( fromBare $
              pure @Allocator $
                \env ->
                  advising
                    ( adviseRecord @Top @Top \method ->
                        keepCallStack ioEx method
                    )
                    (makeController2Loggers env)
          )
          denv
      allocators = pullPhase denv'
      action =
        runContT allocators \constructors -> do
          -- here we complete the construction of the environment
          let (asCall -> call) = fixEnv constructors
          A.runFinalDepT (pure (Constant [])) (call route) 1 2
          pure ()
  me <- try @SyntheticStackTraceException action
  case me of
    Left (SyntheticStackTraceException (fromException @IOError -> Just ex) trace) ->
      assertEqual "exception with callstack" expectedExceptionTagged (ex, trace)
    Right _ -> assertFailure "expected exception did not appear"

tests :: TestTree
tests =
  testGroup
    "All"
    [ testCase "synthetic call stack" testSyntheticCallStack,
      testCase "synthetic call stack with Tagged" testSyntheticCallStackTagged,
      testCase "missing deps" testMissingDeps,
      testCase "synthetic call stack - DepT" testSyntheticCallStack',
      testCase "synthetic call stack with Tagged - DepT" testSyntheticCallStackTagged',
      testCase "missing deps - DepT" testMissingDeps',
      testCase "synthetic call stack - constructor + DepT" testSyntheticCallStack'',
      testCase "synthetic call stack with Tagged - constructor + DepT" testSyntheticCallStackTagged''
    ]

main :: IO ()
main = defaultMain tests
