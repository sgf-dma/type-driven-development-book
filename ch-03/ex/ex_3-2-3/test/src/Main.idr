module Main

import Lib

import Data.Vect

testResults : List Bool
testResults =
  [
    myLength [1..10] == 10
  , myReverse [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] == [10, 9, 8,7, 6, 5, 4, 3, 2, 1]
  , myMap (*2) [1..10] == [2, 4, 6, 8, 10, 12, 14, 16, 18, 20]
  , myMapV length [the String "Hot", "Dog", "Jumping", "Frog"] == [3, 3, 7, 4]
  ]

main : IO ()
main = if all id testResults
          then putStrLn "Test successful!"
          else putStrLn ("Something failed: " ++ show testResults)
