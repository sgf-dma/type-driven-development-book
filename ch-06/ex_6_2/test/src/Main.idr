module Main

import Lib
import Data.Vect

testMatrix : Matrix 2 3
testMatrix = [[0, 0, 0], [0, 0, 0]]

testResults : List Bool
testResults =
  [ printf "%c %f" 'X' 24 == "'X' 24.0"
  ]

testTupleVect : TupleVect 4 Nat
testTupleVect = (1, 2, 3, 4, ())

main : IO ()
main = if all id testResults
          then putStrLn "Test successful!"
          else putStrLn ("Test failed: " ++ show testResults)
