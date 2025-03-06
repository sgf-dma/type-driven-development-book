module Lib

import Data.String
import System

readNumber : IO (Maybe Nat)
readNumber = do
  str <- getLine
  pure $ if all isDigit (unpack str) then Just (stringToNatOrZ str) else Nothing

export
guess : Nat -> IO ()
guess n = do
  putStr "Enter a number: "
  Just k <- readNumber | Nothing => putStrLn "Not a number" >> guess n
  case compare k n of
       LT => putStrLn "Too low" >> guess n
       EQ => putStrLn "Ura!"
       GT => putStrLn "Too high" >> guess n

export
guess2 : Nat -> IO ()
guess2 n = guess' 0
 where
   guess' : Nat -> IO ()
   guess' attempts = do
     let suff = "(" ++ show attempts ++ ")"
     putStr ("Enter a number " ++ suff ++ ": ")
     Just k <- readNumber | Nothing => do
                               putStrLn "Not a number"
                               guess' attempts
     let cont = guess' (attempts + 1)
     case compare k n of
          LT => putStrLn "Too low" >> cont
          EQ => putStrLn ("Ura! " ++ suff)
          GT => putStrLn "Too high" >> cont

export
chooseNumber : IO Nat
chooseNumber = do
  t <- time
  pure . integerToNat $ t `mod` 10

