module Main

import Lib

testResults : List Bool
testResults =
  [ pictureArea testPicture == 328.53981633974485 ]

main : IO ()
main = if all id testResults
          then putStrLn "Test successful!"
          else putStrLn $ "Test failed: " ++ show testResults
