module Lib

import Data.String


%default total

data InfIO : Type where
  Do : IO a -> (a -> Inf InfIO) -> InfIO

data Fuel = Dry | More (Lazy Fuel)

run : Fuel -> InfIO -> IO ()
run (More fuel) (Do c f) =
  do res <- c
     run fuel (f res)
run Dry p = putStrLn "Out of fuel"

partial
forever : Fuel
forever = More forever

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

(>>) : IO a -> Inf InfIO -> InfIO
(>>) mx mb = Do mx (\_ => mb)

totalREPL : (prompt: String) -> (action : String -> String) -> InfIO
totalREPL prompt f = do
  putStr prompt
  line <- getLine
  putStr (f line)
  totalREPL prompt f
