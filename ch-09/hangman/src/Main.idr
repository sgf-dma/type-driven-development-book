
module Main

import Decidable.Equality
import Data.String
import Data.Vect
import Data.Vect.Elem
import Data.List1

import Lib

main : IO ()
main = do
  let word = "AAB"
  case newWordState 3 word of
       Just (letters@(S _) ** w) => game w >>= printLn
       Just (Z ** _) => printLn "Empty word, nothing to guess"
       Nothing => printLn $ "Invalid word: '" ++ word ++ "'. Only capital letters allowed."
