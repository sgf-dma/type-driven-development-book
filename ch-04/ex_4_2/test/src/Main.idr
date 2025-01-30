module Main

import Data.Vect
import Lib

testResults : List Bool
testResults =
  [ vectTake 3 [1,2,3,4,5,6,7] == [1,2,3]
  , vectTake' (FS' (FS' (FS' FZ'))) [1,2,3,4,5,6,7] == [1,2,3]
  , sumEntries 2 [1,2,3,4] [5,6,7,8] == Just 10
  , sumEntries 3 [1,2,3,4] [5,6,7,8] == Just 12
  , sumEntries 4 [1,2,3,4] [5,6,7,8] == Nothing
  , sumEntries' 2 [1,2,3,4] [5,6,7,8] == Just 10
  , sumEntries' 3 [1,2,3,4] [5,6,7,8] == Just 12
  , sumEntries' 4 [1,2,3,4] [5,6,7,8] == Nothing
  ]

main : IO ()
main = if all id testResults
          then putStrLn "Test successful!"
          else putStrLn ("Test failed: " ++ show testResults)
