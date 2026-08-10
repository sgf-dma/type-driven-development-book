
module Quiz

import Data.Bits
import Data.Fin
import Data.Primitives.Views
import Data.String

%default total


export
randoms : Integer -> Stream Integer
randoms seed =
  let seed' = 1664525 * seed + 1013904223 in (seed' `shiftR` 2) :: randoms seed'

-- Use 'Int16', because otherwise conversion to 'Nat' would take too long.
randomsInt : Int16 -> Stream Int16
randomsInt seed =
  let seed' = 1664525 * seed + 1013904223 in (seed' `shiftR` 2) :: randomsInt seed'

record Score where
  constructor MkScore
  -- FIXME: correct : Fin (S (attempted))
  correct : Nat
  attempted : Nat

record GameState where
  constructor MkGameState
  score : Score
  difficulty : Nat

initState : GameState
initState = MkGameState (MkScore 0 0) 12

addCorrect : GameState -> GameState
addCorrect = {score->correct $= (+1), score->attempted $= (+1)}

addWrong : GameState -> GameState
addWrong = {score->attempted $= (+1)}

Show GameState where
  show st = show (correct (score st)) ++ "/" ++
            show (attempted (score st)) ++ "\n" ++
            "Difficulty: " ++ show (difficulty st)

namespace  Command
  public export
  data Command : Type -> Type where
    PutStr : String -> Command ()
    GetLine : Command String
    -- FIXME: GetRandom : Command (Fin (S difficulty))
    GetRandom : Command Nat
    GetGameState : Command GameState
    PutGameState : GameState -> Command ()

    Pure : ty -> Command ty
    Bind : Command a -> (a -> Command b) -> Command b

Functor Command where
  map f c = Bind c (Pure . f)

Applicative Command where
  pure = Pure
  mf <*> mx = Bind mf (\f => Bind mx (Pure . f))

Monad Command where
  (>>=) = Bind

namespace CommandDo
  export
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind
  export
  (>>) : Command a -> Command b -> Command b
  (>>) ma mb = ma >>= (\_ => mb)

runCommand : Stream Integer -> GameState -> Command a -> IO ((GameState, Stream Integer), a)
runCommand rs s0 (PutStr x) = ((s0, rs),) <$> putStr x
runCommand rs s0 GetLine = ((s0, rs),) <$> getLine
runCommand (r::rs') s0 GetRandom = do
  let d = difficulty s0
  -- I don't understand, why should i use `with divides` instead of simple
  -- value-level integer division, when proofs are not used anywhere?
  pure ((s0, rs'), integerToNat r `mod` d)
runCommand rs s0 GetGameState = pure ((s0, rs), s0)
runCommand rs s0 (PutGameState s1) = pure ((s1, rs), ())
runCommand rs s0 (Pure x) = pure ((s0, rs), x)
runCommand rs0 s0 (Bind c f) = do
  ((s1, rs1), x) <- runCommand rs0 s0 c
  runCommand rs1 s1 (f x)

data Fuel = Dry | More (Lazy Fuel)

partial
foreverFuel : Fuel
foreverFuel = More foreverFuel

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  CDo : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  export
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = CDo
  export
  (>>) : Command a -> Inf (ConsoleIO b) -> ConsoleIO b
  (>>) ma mb = ma >>= (\_ => mb)

run : Fuel -> Stream Integer -> GameState -> ConsoleIO a -> IO (GameState, Maybe a)
run _           rs s0 (Quit val) = do pure (s0, Just val)
run (More fuel) rs s0 (CDo c f) = do
  ((s0, rs), res) <- runCommand rs s0 c
  run fuel rs s0 (f res)
run Dry _ s0 _ = pure (s0, Nothing)

data Input = Answer Integer | Retry | QuitCmd

total
readInput : (prompt : String) -> Command Input
readInput prompt = do
  PutStr prompt
  answer <- GetLine
  case answer of
       "" => Pure Retry
       "quit" => Pure QuitCmd
       smth => Pure (Answer (cast smth))

-- Ex 1.
updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = GetGameState >>= PutGameState . f

correct : Command ()
correct = do
  PutStr "Correct!\n"
  updateGameState addCorrect

wrong : Nat -> Command ()
wrong ans = do
  PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
  updateGameState addWrong

quiz : ConsoleIO GameState
quiz = do
  num1 <- GetRandom
  num2 <- GetRandom
  st <- GetGameState
  PutStr (show st ++ "\n")

  let turn : ConsoleIO GameState
      turn = do
        answer <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
        case answer of
             Retry => turn
             QuitCmd => Quit st
             Answer a => if integerToNat a == num1*num2
                            then correct >> quiz
                            else wrong (num1*num2) >> quiz
  turn

partial
main : IO ()
main = do
  (st, res) <- run foreverFuel [1..] initState quiz
  case res of
       Nothing => putStrLn ("Out of fuel")
       Just _ => putStrLn ("Final score: " ++ show st)
