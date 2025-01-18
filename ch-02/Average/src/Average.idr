module Average

import Data.String
import Data.List

export
||| Calculate the averate length of words in a string.
||| @ str a string containing words separated by whitespace.
average : (str : String) -> Double
average str = let numWords = wordCount str
                  totalLength = sum (allLengths (words str)) in
                  cast totalLength / cast numWords
  where
      wordCount : String -> Nat
      wordCount str = length (words str)
      allLengths : List String -> List Nat
      allLengths strs = map length strs

