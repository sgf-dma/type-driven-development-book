module Lib

import Decidable.Equality
import Data.String
import Data.Vect
import Data.Vect.Elem

public export
data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
  MkWordState : (word : String) ->
                (missing : Vect letters Char) ->
                WordState guesses_remaining letters

data Finished : Type where
  Lost : {letters : Nat} -> WordState 0 (S letters) -> Finished
  Won  : {guesses : Nat} -> WordState (S guesses) 0 -> Finished

export
Show Finished where
  show (Lost {letters = letters} (MkWordState word _)) = "You've lost."
            ++ " The word was '" ++ word ++ "'."
            ++ " Letters remaining " ++ show letters
  show (Won {guesses = guesses} (MkWordState word _)) = "You win! "
            ++ " The word was '" ++ word ++ "'."
            ++ " Remaining guesses " ++ show guesses

data ValidInput : List Char -> Type where
  Letter : (c : Char) -> ValidInput [c]

Uninhabited (ValidInput []) where
  uninhabited (Letter _) impossible
Uninhabited (ValidInput (_::_::_)) where
  uninhabited (Letter _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No uninhabited
isValidInput [c] = Yes (Letter c)
isValidInput (_::_::_) = No uninhabited

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

readGuess : IO (x ** ValidInput x)
readGuess = do
  putStr "Guess: "
  s <- getLine
  case isValidString (toUpper s) of
  --case isValidInput (unpack (toUpper s)) of
       Yes prf => pure (_ ** prf)
       No contra => do
         putStrLn "Invalid input, must be single character"
         readGuess

myIsElem : DecEq a => (x : a) -> (xs : Vect n a) -> Dec (Elem x xs)
myIsElem x [] = No uninhabited
myIsElem x (y :: ys) =
  case decEq x y of
       Yes prf => rewrite prf in Yes Here
       No notHere => case myIsElem x ys of
              Yes later => Yes (There later)
              No notThere => No $ \e => case e of
                  Here => notHere Refl
                  There later => notThere later

processGuess : (letter : Char) ->
               WordState (S guesses) (S letters) ->
               Either (WordState guesses (S letters))
                      (WordState (S guesses) letters)
processGuess c (MkWordState word missing) =
  case myIsElem c missing of
       Yes prf => let r = dropElem missing prf in Right (MkWordState word r)
       No contr => Left (MkWordState word missing)

export
game : {guesses : Nat} -> {letters : Nat} -> WordState (S guesses) (S letters) -> IO Finished
game {guesses = guesses} {letters = letters} state = do
  (_ ** Letter c) <- readGuess
  case processGuess c state of
       Left l => do
         putStrLn ("Wrong! Attempts remaining " ++ show guesses)
         case guesses of
              Z => pure (Lost l)
              (S _) => game l
              {-
       Right r => case r of
                       (MkWordState _ []) => pure (Won r)
                       (MkWordState _ (_::_)) => game r
                       -}
       Right r => case letters of
                       Z => pure (Won r)
                       (S _) => game r

