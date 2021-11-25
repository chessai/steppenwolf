{-# language
    BangPatterns
  , DerivingStrategies
  , GeneralisedNewtypeDeriving
  , LambdaCase
  , PackageImports
  , RecordWildCards
  , ScopedTypeVariables
  , StrictData
  , TypeApplications
  , TypeFamilies
#-}

{-# options_ghc -Wall #-}

{-
-}
module Steppenwolf
  ( Steppen(..)
  , WatchPoint(..)
  , Focusedness(..)
  , State
  , debug
  ) where

import "base" Control.Exception (bracket_)
import "base" Control.Monad (void)
import "base" Control.Monad.IO.Class (MonadIO, liftIO)
import "base" Data.Char (isSpace)
import "base" Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import "base" Data.Kind (Type)
import "base" System.IO (BufferMode(..), hFlush, hSetBuffering, hSetEcho, stdin, stdout)
import "base" Text.Read (readMaybe)
import "containers" Data.Map.Strict (Map)
import qualified "containers" Data.Map.Strict as Map
import "edit-distance" Text.EditDistance (levenshteinDistance, defaultEditCosts)
import "mtl" Control.Monad.Reader (ReaderT, runReaderT)
import "mtl" Control.Monad.Reader.Class (MonadReader, ask)
import "transformers" Control.Monad.Trans.Class (lift)

{-
data Fib = Fib { a :: Integer, b :: Integer }

type instance State Fib = Fib

steppenFib :: Steppen Fib
steppenFib = Steppen { initialState = Fib 0 1, transition = \(Fib x y) -> Fib y (x + y), watchPoints = [ WatchPoint Focused "a" (show . a), WatchPoint Focused "b" (show . b) ] }

main = debug steppenFib
-}

-- | A 'WatchPoint' is made up of three things:
--
--   * An introspector: A function which takes a 'State' and outputs some debugging information
--   * A name: The name of the watchpoint
--   * A focusedness: 'Focused' means that we care about the watchpoint at that time, 'Unfocused' means it will be left out.
data WatchPoint a = WatchPoint
  { focused :: Focusedness
  , name :: String
  , introspector :: State a -> String
  }

-- | The 'Focusedness' of a 'WatchPoint' determines whether the watchpoint is in focus or out of focus.
data Focusedness = Focused | Unfocused
  deriving stock (Eq, Ord, Read, Show)

-- | The 'State' of a point in debugging.
type family State (a :: Type) :: Type

-- | A 'Steppen' is made up of three things:
--
--   * An initial state: The initial state of the debugger
--   * A transition function: A function which updates the state of the debugger
--   * A list of watchpoints: 'WatchPoints' that scrutinise on the state
--
--   It can be consumed using the 'debug' function, which initiates a debugging session.
data Steppen a = Steppen
  { initialState :: State a
  , transition :: State a -> State a
  , watchPoints :: [WatchPoint a]
  }

-- only used internally
type Name = String

-- | Initiate a debugging session given a 'Steppen'
debug :: ()
  => Steppen a
  -> IO ()
debug st = do
  hSetEcho stdin False 
  hSetBuffering stdin NoBuffering 
  initialDebugState <- newIORef $ DebugState 
    { bufferSize = 30
    , stepSize = 1
    , watchPointNames = Map.fromList (map (\wp -> (name wp, focused wp)) (watchPoints st))
    }
  runDebug initialDebugState (debugLoop st (initialState st) [])

debugLoop :: forall a. ()
  => Steppen a
  -> State a
  -> [State a]
  -> Debug ()
debugLoop st = go
  where
    go s history = do
      prettyIntrospection st s
      execute s history =<< getCommand

    execute :: State a -> [State a] -> Command -> Debug ()
    execute s history = \case

      Move d -> do
        steps <- get stepSize
        let (s', history') = move steps s history d
        go s' history'

      SetStepSize -> do
        currentStepSize <- get stepSize
        put $ "Input new step size (current: " ++ show currentStepSize ++ "): "
        newStepSizeStr <- strip <$> getLn Echo
        putLn ""
        case readMaybe @Int newStepSizeStr of
          Nothing -> do
            putLn $ "Invalid step size: " ++ newStepSizeStr
            go s history
          Just newStepSize -> do
            updateStepSize newStepSize
            go s history

      SetBufferSize -> do
        currentBufferSize <- get bufferSize
        put $ "Input new buffer size (current: " ++ show currentBufferSize ++ "): "
        newBufferSizeStr <- strip <$> getLn Echo
        putLn ""
        case readMaybe @Int newBufferSizeStr of
          Nothing -> do
            putLn $ "Invalid buffer size: " ++ newBufferSizeStr
            go s history
          Just newBufferSize -> do
            updateBufferSize newBufferSize
            go s history

      Focus -> do
        currentWatchpoints <- get watchPointNames
        if all (== Focused) currentWatchpoints
          then do
            putLn "All watchpoints are in focus. Focusing harder can't help."
            putLn "Did you mean to unfocus a watchpoint? If so, try 'u'."
            putLn ""
            go s history
          else do
            put "Enter the watchpoint to add as a focal point: "
            name <- strip <$> getLn Echo
            if null name
              then do
                putLn "That was empty!"
                go s history
              else do
                putLn ""
                newWatchpoints <- Map.alterF
                  (\case
                    Nothing -> do
                      putLn $ "'" ++ name ++ "' is not a watchpoint."
                      didYouMean name (Map.keys currentWatchpoints)
                      pure Nothing
                    Just Focused -> do
                      putLn $ "'" ++ name ++ "' is already a focal point. Did you mean to unfocus it? If so, try 'u'."
                      putLn ""
                      pure (Just Focused)
                    Just Unfocused -> do
                      pure (Just Focused)
                  ) name currentWatchpoints
                updateWatchpoints (const newWatchpoints)
                go s history

      Unfocus -> do
        currentWatchpoints <- get watchPointNames
        if all (== Unfocused) currentWatchpoints
          then do
            putLn "All watchpoints are out of focus."
            putLn "Did you mean to focus on a watchpoint? If so, try 'f'."
            go s history
          else do
            put "Enter the watchpoint to unfocus: "
            name <- strip <$> getLn Echo
            if null name
              then do
                putLn "That was empty!"
                go s history
              else do
                putLn ""
                newWatchpoints <- Map.alterF
                  (\case
                    Nothing -> do
                      putLn $ "'" ++ name ++ "' is not a watchpoint."
                      didYouMean name (Map.keys currentWatchpoints)
                      pure Nothing
                    Just Focused -> do
                      pure (Just Unfocused)
                    Just Unfocused -> do
                      putLn $ "'" ++ name ++ "' is already unfocused. Did you mean to make it a focal point? If so, try 'f'."
                      pure (Just Unfocused)
                  ) name currentWatchpoints
                updateWatchpoints (const newWatchpoints)
                go s history

      Quit -> do
        putLn quitMessage

      Help -> do
        putLn helpMessage
        _ <- getChr
        go s history

      Unrecognised -> do
        putLn unrecognisedMessage
        go s history

    move :: Int -> State a -> [State a] -> Direction -> (State a, [State a])
    move steps s history d = performSteps 0 (s, history)
      where
        performSteps :: Int -> (State a, [State a]) -> (State a, [State a])
        performSteps !step (!x, !xs)
          | step < steps = case d of
              Forward -> performSteps (step + 1) (stepForward x xs)
              Backward -> performSteps (step + 1) (stepBackward xs)
          | otherwise = (x, xs)

    stepForward :: ()
      => State a
      -> [State a]
      -> (State a, [State a])
    stepForward s previous = (transition st s, (s : previous))

    stepBackward :: ()
      => [State a]
      -> (State a, [State a])
    stepBackward = \case
      [] -> (initialState st, [])
      (s : ss) -> (s, ss)

newtype Debug a = Debug (ReaderT (IORef DebugState) IO a)
  deriving newtype (Functor, Applicative, Monad)
  deriving newtype (MonadIO)
  deriving newtype (MonadReader (IORef DebugState))
  deriving newtype (Io)

data DebugState = DebugState
  { bufferSize :: Int
  , stepSize :: Int
  , watchPointNames :: Map Name Focusedness
  }

runDebug :: IORef DebugState -> Debug a -> IO a
runDebug s (Debug d) = runReaderT d s

update :: (DebugState -> DebugState) -> Debug ()
update f = do
  state <- ask
  liftIO $ modifyIORef' state f

updateBufferSize :: Int -> Debug ()
updateBufferSize newBufferSize = update $ \DebugState{..} ->
  DebugState{bufferSize = newBufferSize, ..}

updateStepSize :: Int -> Debug ()
updateStepSize newStepSize = update $ \DebugState{..} ->
  DebugState{stepSize = newStepSize, ..}

updateWatchpoints :: (Map Name Focusedness -> Map Name Focusedness) -> Debug ()
updateWatchpoints f = update $ \DebugState{..} ->
  DebugState{watchPointNames = f watchPointNames, ..}

get :: (DebugState -> a) -> Debug a
get f = do
  state <- ask
  liftIO $ fmap f $ readIORef state

rpad :: Int -> [Char] -> [Char]
rpad padding xs = take padding (xs ++ repeat ' ')

pad :: Int -> Name -> String -> String
pad padding name value = rpad padding (name ++ ":") ++ value

prettyIntrospection :: ()
  => Steppen a
  -> State a
  -> Debug ()
prettyIntrospection st s = do
  ws <- get watchPointNames
  bufSize <- get bufferSize
  -- TODO: this is bad perf. fix this.
  let rabbitHole = Map.fromList
        $ map (\w -> (name w, introspector w s))
        $ watchPoints st
  let lookingGlass name = Map.findWithDefault (error "lookingGlass: internal error") name rabbitHole
  void $ flip Map.traverseWithKey ws $ \name -> \case
    Focused -> do
      putLn (pad bufSize name (lookingGlass name))
    Unfocused -> do
      pure ()
  putLn ""

data Command
  = Help
  | Quit
  | Move Direction
  | SetBufferSize
  | SetStepSize
  | Unrecognised
  | Focus
  | Unfocus
  deriving stock (Eq, Show)

data Direction = Forward | Backward
  deriving stock (Eq, Show)

unrecognisedMessage :: String
unrecognisedMessage = "Unrecognised command. Try typing 'h' for help?"

helpMessage :: String
helpMessage = unlines
  [ fmt "h" "Display this help message"
  , fmt "q" "Exit the debugger"
  , fmt "n" "Step forward"
  , fmt "p" "Step backward"
  , fmt "s" "Set step size"
  , fmt "b" "Set buffer size"
  , fmt "f" "Focus on things"
  , fmt "u" "Unfocus on things"
  , ""
  , "Press any key to resume."
  ]
  where
    fmt lhs rhs = lhs ++ ": " ++ rhs

quitMessage :: String
quitMessage = "Quitting. Bye!"

strip :: String -> String
strip = reverse . go . reverse . go
  where
    go [] = []
    go s@(c:cs) = if isSpace c then go cs else s

getCommand :: Debug Command
getCommand = do
  c <- getChr
  case c of
    'n' -> pure (Move Forward)
    'p' -> pure (Move Backward)
    'q' -> pure Quit
    'h' -> pure Help
    's' -> pure SetStepSize
    'b' -> pure SetBufferSize
    'f' -> pure Focus
    'u' -> pure Unfocus
    _ -> pure Unrecognised

class Monad f => Io f where
  put :: String -> f ()
  putLn :: String -> f ()

  getChr :: f Char
  getLn :: Echo -> f String

data Echo = Echo | NoEcho

instance Io IO where
  put s = do
    putStr s
    hFlush stdout
  putLn s = do
    putStrLn s
    hFlush stdout

  getChr = getChar
  getLn = \case
    Echo -> withEcho getLineWithBuffering
    NoEcho -> withNoEcho getLineWithBuffering

withNoEcho :: IO a -> IO a
withNoEcho x = bracket_
  (hSetEcho stdin False)
  (hSetEcho stdin True)
  x

withEcho :: IO a -> IO a
withEcho x = bracket_
  (hSetEcho stdin True)
  (hSetEcho stdin False)
  x

-- allows users to backspace inside of ghci
getLineWithBuffering :: IO String
getLineWithBuffering = bracket_
  (hSetBuffering stdin LineBuffering)
  (hSetBuffering stdin NoBuffering)
  getLine

instance (Io f) => Io (ReaderT r f) where
  put = lift . put
  putLn = lift . putLn

  getChr = lift getChr
  getLn = lift . getLn

-- TODO: make this have slightly better UX
didYouMean :: (Io f) => Name -> [Name] -> f ()
didYouMean name names = go closeOnes
  where
    closeOnes :: [Name]
    closeOnes = id
      $ map fst
      $ filter ((<= 2) . snd)
      $ map (\n -> (n, levenshteinDistance defaultEditCosts name n))
      $ names

    go = \case
      [] -> do
        pure ()
      [x] -> do
        putLn $ "Did you mean `" ++ x ++ "`?"
        putLn ""
      xs -> do
        putLn $ "Did you mean one of:"
        mapM_ (putLn . ("  " ++)) xs
        putLn ""
