
module Main

import Decidable.Equality
import Data.String
import Data.Vect
import Data.Vect.Elem
import Data.List1

import Lib


-- Find all unique letters from a list. For calling `game` i need letters
-- greater, than 0. This function can guarantee that.
uniqueLetters : {n : Nat} -> List1 Char -> Vect n Char -> (m ** Vect (S m) Char)
uniqueLetters {n = n} (x:::[]) acc =
  -- I need 'Elem x xs' proof here to deduce, that 'acc' has at least one
  -- element, when element was found.
  case isElem x acc of
       Yes Here => (_ ** acc)
       Yes (There later) => (_ ** acc)
       No _ => (n ** x::acc)
uniqueLetters {n = n} (x:::(x2::xs)) acc =
  -- I may use `isElem` here too, but because i don't need proof `elem` is
  -- enough.
  case elem x acc of
       True  => uniqueLetters (x2:::xs) acc
       False => uniqueLetters (x2:::xs) (x::acc)

main2 : IO ()
main2 = do
  let (m ** letters) = uniqueLetters ('t' ::: (unpack "est")) []
      w = MkWordState {guesses_remaining = 3} "test" (map toUpper letters)
  game w >>= printLn

