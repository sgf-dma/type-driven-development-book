module Main

import Lib

import Data.Vect

testResults : List Bool
testResults =
  [
    transposeMat [[1,2], [3,4], [5,6]]
      == [[1,3,5], [2,4,6]]
  , addMatrix [[1,2],[3,4]] [[5,6], [7,8]]
      == [[6,8], [10,12]]
  , multMatrix [[1,2], [3,4], [5,6]] [[7,8,9,10], [11,12,13,14]]
      == [[29, 32, 35, 38],
          [65, 72, 79, 86],
          [101,112,123,134]]
  ]

main : IO ()
main = if all id testResults
          then putStrLn "Test successful!"
          else putStrLn ("Something failed: " ++ show testResults)
