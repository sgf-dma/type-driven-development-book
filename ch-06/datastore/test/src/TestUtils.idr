
module TestUtils

import Data.Vect

import Utils

export
testUtilsData : List Bool
testUtilsData =
  [ padEmpty 0 [] == the (Vect _ (List String)) [[]]
  , padEmpty 1 [] == the (Vect _ (List String)) [[], []]
  , padEmpty 0 [["a"], ["b"]] == [["a"], ["b"]]
  , padEmpty 1 [["a"], ["b"]] == [["a"], ["b"]]
  , padEmpty 2 [["a"], ["b"]] == [["a"], ["b"], []]
  ]
