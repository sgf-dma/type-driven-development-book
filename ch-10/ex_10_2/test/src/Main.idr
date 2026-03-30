module Main

import Data.Vect
import Data.List
import Data.Nat
import Data.Nat.Views

import Lib


testEqualSuffix : List Bool
testEqualSuffix =
  [ equalSuffix [1,2,4,5] [1..5] == [4,5]
  , equalSuffix [1,2,4,5,6] [1..5] == []
  , equalSuffix [1,2,4,5,6] [1..6] == [4,5,6]
  ]

testHalfNat : List Bool
testHalfNat =
  [ halfNat 0 == EvenHalf 0
  , halfNat 1 == OddHalf 0
  , halfNat 2 == EvenHalf 1
  , halfNat 3 == OddHalf 1
  , halfNat 4 == EvenHalf 2
  , halfNat 5 == OddHalf 2
  ]

testVectSplitHalf : List Bool
testVectSplitHalf =
  [ vectSplitHalf {a = Int} {n = Z} [] == VSplitEven {a = Int} {k = Z} [] []
  , vectSplitHalf [1] == VSplitOdd [] [1]
  , vectSplitHalf [1,2] == VSplitEven [1] [2]
  , vectSplitHalf [1,2,3] == VSplitOdd [1] [2,3]
  , vectSplitHalf [1,2,3,4] == VSplitEven [1,2] [3,4]
  , vectSplitHalf [1,2,3,4,5] == VSplitOdd [1,2] [3,4,5]
  ]

testMySplitRecV : List Bool
testMySplitRecV =
  [ mySplitRecV {a = Int} [] == MyRecVNil
  , mySplitRecV [1] == MyRecVOne
  , mySplitRecV [1,2] == MyRecVPair [1] [2] MyRecVOne MyRecVOne
  , mySplitRecV [1,2,3] == MyRecVPair [1] [2,3]
                                MyRecVOne
                                (MyRecVPair [2] [3] MyRecVOne MyRecVOne)
  , mySplitRecV [1,2,3,4] == MyRecVPair [1,2] [3,4]
                                (MyRecVPair [1] [2] MyRecVOne MyRecVOne)
                                (MyRecVPair [3] [4] MyRecVOne MyRecVOne)
  ]

testMergeSort : List Bool
testMergeSort = 
  [ mergeSort [3,2,1] == [1,2,3]
  , mergeSort [5,1,4,3,2,6,8,7,9] == [1,2,3,4,5,6,7,8,9]
  ]

testMyHalfRec : List Bool
testMyHalfRec =
  [ toListHalfRecMy (myHalfRec 0) == toListHalfRec (halfRec 0)
  , toListHalfRecMy (myHalfRec 1) == toListHalfRec (halfRec 1)
  , toListHalfRecMy (myHalfRec 2) == toListHalfRec (halfRec 2)
  , toListHalfRecMy (myHalfRec 3) == toListHalfRec (halfRec 3)
  , toListHalfRecMy (myHalfRec 4) == toListHalfRec (halfRec 4)
  , toListHalfRecMy (myHalfRec 5) == toListHalfRec (halfRec 5)
  , toListHalfRecMy (myHalfRec 7) == toListHalfRec (halfRec 7)
  , toListHalfRecMy (myHalfRec 9) == toListHalfRec (halfRec 9)
  , toListHalfRecMy (myHalfRec 10) == toListHalfRec (halfRec 10)
  ]

testToBinary : List Bool
testToBinary =
  [ toBinary 0 == ""
  , toBinary 1 == "1"
  , toBinary 2 == "10"
  , toBinary 3 == "11"
  , toBinary 4 == "100"
  , toBinary 7 == "111"
  , toBinary 42 == "101010"
  , toBinary 94 == "1011110"
  ]

testHalfList : List Bool
testHalfList =
  [ halfList {a = Int} [] == Halves [] [] []
  , halfList [1] == Halves [] [1] []
  , halfList [1,2] == Halves [1] [] [2]
  , halfList [1..3] == Halves [1] [2] [3]
  , halfList [1..4] == Halves [1,2] [] [3,4]
  , halfList [1..5] == Halves [1,2] [3] [4,5]
  ]

testMyVList : List Bool
testMyVList =
  [ myVList {a = Int} [] == MyVNil
  , myVList [1] == MyVOne
  , myVList [1,2] == MyVCons {x = 1} {y = 2} MyVNil
  , myVList [1..3] == MyVCons (MyVOne {x = 2})
  , myVList [1..4] == MyVCons {x = 1} {y = 4} (MyVCons {x = 2} {y = 3} MyVNil)
  , myVList [1..5] == MyVCons {x = 1} {y = 5} (MyVCons {x = 2} {y = 4} (MyVOne {x  = 3}))
  ]

testMyVList' : List Bool
testMyVList' =
  [ myVList' {a = Int} [] == MyVNil
  , myVList' [1] == MyVOne
  , myVList' [1,2] == MyVCons {x = 1} {y = 2} MyVNil
  , myVList' [1..3] == MyVCons (MyVOne {x = 2})
  , myVList' [1..4] == MyVCons {x = 1} {y = 4} (MyVCons {x = 2} {y = 3} MyVNil)
  , myVList' [1..5] == MyVCons {x = 1} {y = 5} (MyVCons {x = 2} {y = 4} (MyVOne {x  = 3}))
  ]

testPalindrome : List Bool
testPalindrome =
  [ palindrome (unpack "") == True
  , palindrome (unpack "a") == True
  , palindrome (unpack "ab") == False
  , palindrome (unpack "aa") == True
  , palindrome (unpack "aba") == True
  , palindrome (unpack "abccba") == True
  , palindrome (unpack "abcba") == True
  , palindrome (unpack "abcb") == False
  ]

runTest : Show b => (name : String)
        -> (acc0 : a)
        -> (run : (acc : a) -> b -> Maybe a)
        -> List b -> IO ()
runTest name acc0 run ts =
    let n = length ts
    in  either
          (\err => putStrLn ("Test '" ++ name ++ "' failed with " ++ show err))
          (\_   => putStrLn ("Test '" ++ name ++ "' successful!"))
          $ foldl go (Right acc0) (zip [0..n] ts)
  where
    go : Either (Nat, String) a -> (Nat, b) -> Either (Nat, String) a
    go err@(Left _) _ = err
    go (Right acc) (n, v) =
      case run acc v of
           Nothing => Left (n, show v)
           Just acc' => Right acc'

checkBool : a -> Bool -> Maybe a
checkBool _ False = Nothing
checkBool v True = Just v

main : IO ()
main = do
  runTest "testEqualSuffix" () checkBool testEqualSuffix
  runTest "testHalfNat" () checkBool testHalfNat
  runTest "testMyHalfRec" () checkBool testMyHalfRec
  runTest "testVectSplitHalf" () checkBool testVectSplitHalf
  runTest "testMergeSort" () checkBool testMergeSort
  runTest "testToBinary" () checkBool testToBinary
  runTest "testHalfList" () checkBool testHalfList
  runTest "testMyVList" () checkBool testMyVList
  runTest "testMyVList'" () checkBool testMyVList'
  runTest "testPalindrome'" () checkBool testPalindrome
