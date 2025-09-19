module Lib

import Decidable.Equality
import Data.String
import Data.Vect
import Data.Vect.Elem
import Data.List.Elem

import Vect
import List

-- I want to use only allowed characters anywhere in the game. E.g. for
-- avoiding creating WordState with lower case letters and then trying to
-- guess it using upper case letters (because readGuess calls `toUpper`).
--AllowedChars : Vect _ Char
AllowedChars = the (Vect _ Char) (fromList (rangeFromTo 'A' 'Z'))

public export
data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
  MkWordState : (word : String) ->
                (missing : Vect letters Char) ->
                -- FIXME: 'auto' compiles too long for wrong input.
                {auto allowed : Subset missing AllowedChars} ->
                {guesses_remaining : Nat} ->
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

-- Now i should also ensure, that input character is in allowed chars list.
data ValidInput : List Char -> Type where
  Letter : (c : Char) -> {auto allowed : Elem c AllowedChars} -> ValidInput [c]

Uninhabited (ValidInput []) where
  uninhabited (Letter _) impossible
Uninhabited (ValidInput (_::_::_)) where
  uninhabited (Letter _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No uninhabited
isValidInput [c] =
  case isElem c AllowedChars of
       Yes _ => Yes (Letter c)
       No notAllowed => No $ \(Letter _ {allowed = allowed}) => notAllowed allowed
isValidInput (_::_::_) = No uninhabited

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

-- In fact, i don't need 'Dec', because i don't care about 'contra' proof in
-- readGuess below. I.e. regular 'Maybe' is enough.
isValidStringM : (s : String) -> Maybe (ValidInput (unpack s))
isValidStringM s = case isValidString s of
                         Yes prf => Just prf
                         No _ => Nothing

-- When adding allowed characters verification, i should not change the type
-- returned by 'readGuess', because its type is the type, which _caller_ wants
-- to get, - a list of 'Char's. And therefore predicate (whatever it verifies)
-- should always check value of that type - 'List Char'. In other words,
-- regardless of what exactly predicate 'ValidInput' verifies, predicate type
-- should remain the same: 'List Char -> Type'.
readGuess : IO (xs ** ValidInput xs)
readGuess = do
  putStr "Guess: "
  s <- getLine
  case isValidStringM s of
       Just prf => pure (_ ** prf)
       Nothing => do
         putStrLn "Invalid input: guess should be single capital letter."
         readGuess

processGuess : (letter : Char) ->
               WordState (S guesses) (S letters) ->
               Either (WordState guesses (S letters))
                      (WordState (S guesses) letters)
processGuess c (MkWordState word missing {allowed = allowed}) =
  case isElem c missing of
       -- I need allowed' to be available to prove, that vector resulting from
       -- `dropElem` still is subset of AllowedChars.
       Yes el => let allowed' = dropSubsetElem allowed el
                 in  Right (MkWordState word (dropElem missing el))
       No _ => Left (MkWordState word missing)

export
game : {guesses : Nat} -> {letters : Nat} -> WordState (S guesses) (S letters) -> IO Finished
game {guesses = guesses} {letters = letters} state = do
  (_ ** Letter c) <- readGuess
  case processGuess c state of
       Left l => do
         putStrLn ("Wrong! Mistakes remaining " ++ show guesses)
         case guesses of
              Z => pure (Lost l)
              (S _) => game l
       Right r => case letters of
                       Z => pure (Won r)
                       (S _) => game r

export
newWordState : (guesses_remaining : Nat) ->
               (input : String) ->
               Maybe (letters : Nat ** WordState guesses_remaining letters)
newWordState guesses_remaining input =
  let missing = fromList (uniqueElems (unpack input))
  in  case isSubset missing AllowedChars of
           Yes prf => Just (_ ** MkWordState input missing)
           No _ => Nothing
