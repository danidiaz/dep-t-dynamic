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
-- invocations of monadic functions—though only of those which take part in dependency
-- injection.
--
-- We are assuming that the application follows a "record-of-functions" style.
module Main (main) where

import Control.Exception
import Control.Monad.Dep (DepT)
import Control.Monad.IO.Unlift
import Control.Monad.Reader
import Control.Monad.Trans.Cont
import Data.Function ((&))
import Data.Functor ((<&>))
import Control.Arrow ((>>>))
import Data.Functor.Compose
import Data.Functor.Constant
import Data.Functor.Identity
import Data.IORef
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Typeable
import Dep.Advice qualified as A
import Dep.Advice.Basic qualified as A
import Dep.Has
import Dep.Env
  ( Autowireable,
    Autowired (..),
    Constructor,
    DemotableFieldNames,
    FieldsFindableByType,
    Phased,
    bindPhase,
    constructor,
    fixEnv,
    pullPhase,
    skipPhase,
  )
import Dep.Has
  ( Has (dep),
    asCall,
  )
import Dep.Tagged (Tagged (..), tagged, untag)
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
import Dep.Dynamic
import Dep.SimpleChecked qualified as SC
import Dep.Checked qualified as C
import GHC.Generics (Generic)
import GHC.TypeLits
import Lens.Micro (Lens', lens)
import System.IO
import Test.Tasty
import Test.Tasty.HUnit
import Data.Functor.Const
import Prelude hiding (insert, lookup)

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
data Env h m = Env
  { logger :: h (Logger m),
    logger2 :: h (Tagged "secondary" Logger m),
    repository :: h (Repository m),
    controller :: h (Controller m)
  }
  deriving stock (Generic)
  deriving anyclass (Phased, DemotableFieldNames, FieldsFindableByType)

-- Locate the components by their types. We could also define the required Has
-- instance for each component manually, but that's tedious.
deriving via Autowired (Env Identity m) instance Autowireable r_ m (Env Identity m) => Has r_ m (Env Identity m)

-- The "phases" that components go through until fully built. Each phase
-- is represented as an applicative functor. The succession of phases is
-- defined using Data.Functor.Compose.
--

-- A phase in which we might allocate some resource needed by the component,
-- also set some bracket-like resource management.
-- The "managed" library could be used instead of ContT.
type Allocator = ContT () IO

-- First we allocate any needed resource, then we have a construction phase
-- during which the component reads its own dependencies from a "completed"
-- environment.
--
-- There could be more phases, like for example an initial "read configuration"
-- phase.
type Phases env = Allocator `Compose` Constructor env

-- Environment value
--
-- The base monad is a 'ReaderT' holding a SyntheticCallStack value which gets modified
-- using "local" for each sub-call.
--
-- Notice that neither the interfaces nor the implementations which we defined
-- earlier knew anything about the ReaderT.
env :: Env (Phases (Env Identity (ReaderT SyntheticCallStack IO))) (ReaderT SyntheticCallStack IO)
env =
  Env
    { logger =
        allocateBombs 1 `bindPhase` \bombs ->
          constructor \_ ->
            makeStdoutLogger
              & advising
                ( adviseRecord @Top @Top \method ->
                    keepCallStack ioEx method <> injectFailures bombs
                ),
      logger2 =
        allocateBombs 0 `bindPhase` \bombs ->
          constructor \_ ->
            tagged @"secondary" makeStdoutLogger
              & advising
                ( adviseRecord @Top @Top \method ->
                    keepCallStack ioEx method <> injectFailures bombs
                ),
      repository =
        allocateSet `bindPhase` \ref ->
          constructor \env ->
            makeInMemoryRepository ref env
              & advising
                ( adviseRecord @Top @Top \method ->
                    keepCallStack ioEx method
                ),
      controller =
        skipPhase @Allocator $
          constructor \env ->
            makeController env
              & advising
                ( adviseRecord @Top @Top \method ->
                    keepCallStack ioEx method
                )
    }

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
-- The environment of DepT includes—just as before—the SyntheticCallStack value
-- that is used to trace each sub-call.
--
-- But now it also includes the dependency injection context with all the
-- components.
env' :: Env Phases' (DepT (CallEnv SyntheticCallStack (Env Identity)) IO)
env' =
  Env
    { logger =
        allocateBombs 1 `bindPhase` \bombs ->
          Identity $ A.component \_ ->
            makeStdoutLogger
              & A.adviseRecord @Top @Top \method ->
                A.keepCallStack ioEx method <> A.injectFailures bombs,
      logger2 =
        allocateBombs 0 `bindPhase` \bombs ->
          Identity $ A.component \_ ->
            tagged @"secondary" makeStdoutLogger
              & A.adviseRecord @Top @Top \method ->
                A.keepCallStack ioEx method <> A.injectFailures bombs,
      repository =
        allocateSet `bindPhase` \ref ->
          Identity $ A.component \env ->
            makeInMemoryRepository ref env
              & A.adviseRecord @Top @Top \method ->
                A.keepCallStack ioEx method,
      controller =
        skipPhase @Allocator $
          Identity $ A.component \env ->
            makeController env
              & A.adviseRecord @Top @Top \method ->
                A.keepCallStack ioEx method
    }


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

env'' :: Env (Phases (Env Identity (RT SyntheticCallStack IO))) (RT SyntheticCallStack IO)
env'' = 
  Env
    { logger =
        allocateBombs 1 `bindPhase` \bombs ->
          constructor \_ ->
            makeStdoutLogger
              & A.adviseRecord @Top @Top \method ->
                A.keepCallStack ioEx method <> A.injectFailures bombs,
      logger2 =
        allocateBombs 0 `bindPhase` \bombs ->
           constructor \_ ->
            tagged @"secondary" makeStdoutLogger
              & A.adviseRecord @Top @Top \method ->
                A.keepCallStack ioEx method <> A.injectFailures bombs,
      repository =
        allocateSet `bindPhase` \ref ->
          constructor \env ->
            makeInMemoryRepository ref env
              & A.adviseRecord @Top @Top \method ->
                A.keepCallStack ioEx method,
      controller =
        skipPhase @Allocator $
          constructor \env ->
            makeController env
              & A.adviseRecord @Top @Top \method ->
                A.keepCallStack ioEx method
    }

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
    [ NonEmpty.fromList [
                (typeRep (Proxy @Logger), "emitMsg")
        ,       (typeRep (Proxy @(Tagged "secondary" Logger)), "unTagged")
        ],
      NonEmpty.fromList [(typeRep (Proxy @Controller), "route")]
    ]
  )

-- Test the "Constructor"-based version of the environment.
testSyntheticCallStack :: Assertion
testSyntheticCallStack = do
  let action =
        runContT (pullPhase @Allocator env) \constructors -> do
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
  let envz = env {
          controller =
            skipPhase @Allocator $
              constructor \env ->
                makeController2Loggers env
                  & advising
                    ( adviseRecord @Top @Top \method ->
                        keepCallStack ioEx method
                    )
        }
      action =
        runContT (pullPhase @Allocator envz) \constructors -> do
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


-- Test the "DepT"-based version of the environment.
testSyntheticCallStack' :: Assertion
testSyntheticCallStack' = do
  let action =
        runContT (pullPhase @Allocator env') \runnable -> do
          _ <- A.runFromDep (pure (CallEnv [] runnable)) route 1 2
          pure ()
  me <- try @SyntheticStackTraceException action
  case me of
    Left (SyntheticStackTraceException (fromException @IOError -> Just ex) trace) ->
      assertEqual "exception with callstack" expectedException (ex, trace)
    Right _ -> assertFailure "expected exception did not appear"

testSyntheticCallStackTagged' :: Assertion
testSyntheticCallStackTagged' = do
  let envz = env' {
          controller =
            skipPhase @Allocator $
              Identity $ A.component \env ->
                makeController2Loggers env
                  & A.adviseRecord @Top @Top \method ->
                    A.keepCallStack ioEx method
        }
      action =
        runContT (pullPhase @Allocator envz) \runnable -> do
          _ <- A.runFromDep (pure (CallEnv [] runnable)) route 1 2
          pure ()
  me <- try @SyntheticStackTraceException action
  case me of
    Left (SyntheticStackTraceException (fromException @IOError -> Just ex) trace) ->
      assertEqual "exception with callstack" expectedExceptionTagged (ex, trace)
    Right _ -> assertFailure "expected exception did not appear"



testSyntheticCallStack'' :: Assertion
testSyntheticCallStack'' = do
  let action =
        runContT (pullPhase @Allocator env'') \constructors -> do
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
  let envz = env'' {
          controller =
            skipPhase @Allocator $
              constructor \env ->
                makeController2Loggers env
                  & A.adviseRecord @Top @Top \method ->
                    A.keepCallStack ioEx method
        }
      action =
        runContT (pullPhase @Allocator envz) \constructors -> do
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
      testCase "synthetic call stack - DepT" testSyntheticCallStack',
      testCase "synthetic call stack with Tagged - DepT" testSyntheticCallStackTagged',
      testCase "synthetic call stack - constructor + DepT" testSyntheticCallStack'',
      testCase "synthetic call stack with Tagged - constructor + DepT" testSyntheticCallStackTagged''
    ]

main :: IO ()
main = defaultMain tests
