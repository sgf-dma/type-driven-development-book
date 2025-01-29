module Main

import Lib

testPic1 : Picture
testPic1 = Combine (Primitive (Triangle 2 3))
                   (Primitive (Triangle 2 4))

testPic2 : Picture
testPic2 = Combine (Primitive (Rectangle 1 3))
                   (Primitive (Circle 4))

testResults : List Bool
testResults = [
    listToTree [1, 4, 3, 5, 2]
      == NodeBS (NodeBS EmptyBS 1 EmptyBS)
          2
          (NodeBS (NodeBS EmptyBS
                          3
                          (NodeBS EmptyBS 4 EmptyBS))
                  5
                  EmptyBS)
  , treeToList (listToTree [4,1,8,7,2,3,9,5,6]) == [1..9]
  , evaluate (Mult (Val 10) (Add (Val 6) (Val 3))) == 90
  , maxMaybe (Just 4) (Just 5) == Just 5
  , maxMaybe (Just 4) Nothing == Just 4
  , biggestTriangle testPic1 == Just 4.0
  , biggestTriangle testPic2 == Nothing
  ]

main : IO ()
main = if all id testResults
          then putStrLn "Test successful!"
          else putStrLn ("Test failed: " ++ show testResults)
