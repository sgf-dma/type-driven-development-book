module Main

import Data.Vect
import Lib

main : IO ()
main =
  if myReverse [1,2,3,4] == [4,3,2,1]
     then putStrLn "Test successful!"
     else putStrLn "Test failed!"
