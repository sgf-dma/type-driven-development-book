module Main

import Data.Nat
import Data.Vect
import Data.List

import Remainder
import SnocVect
import Ch5
import Ch6

testRemainder : List Bool
testRemainder =
  [ findRemainder1 0 1 == MkRem1 0 0
  , findRemainder1 1 1 == MkRem1 1 0
  , findRemainder1 5 1 == MkRem1 5 0
  , findRemainder1 5 2 == MkRem1 2 1
  , findRemainder1 5 3 == MkRem1 1 2
  , findRemainder1 5 4 == MkRem1 1 1
  , findRemainder1 5 5 == MkRem1 1 0
  , findRemainder1 5 6 == MkRem1 0 5
  , findRemainder1 5 7 == MkRem1 0 5

  , findRemainder2 1 1 == MkRem2 1 0
  , findRemainder2 5 1 == MkRem2 5 0
  , findRemainder2 5 2 == MkRem2 2 1
  , findRemainder2 5 3 == MkRem2 1 2
  , findRemainder2 5 4 == MkRem2 1 1
  , findRemainder2 5 5 == MkRem2 1 0

  , findRemainder3 1 1 == MkRem2 1 0
  , findRemainder3 5 1 == MkRem2 5 0
  , findRemainder3 5 2 == MkRem2 2 1
  , findRemainder3 5 3 == MkRem2 1 2
  , findRemainder3 5 4 == MkRem2 1 1
  , findRemainder3 5 5 == MkRem2 1 0

  , findRemainder5 0 1 == MkRem1 0 0
  , findRemainder5 1 1 == MkRem1 1 0
  , findRemainder5 5 1 == MkRem1 5 0
  , findRemainder5 5 2 == MkRem1 2 1
  , findRemainder5 5 3 == MkRem1 1 2
  , findRemainder5 5 4 == MkRem1 1 1
  , findRemainder5 5 5 == MkRem1 1 0
  , findRemainder5 5 6 == MkRem1 0 5
  , findRemainder5 5 7 == MkRem1 0 5

  , findRemainder 0 1 == MkRem 0 0
  , findRemainder 1 1 == MkRem 1 0
  , findRemainder 5 1 == MkRem 5 0
  , findRemainder 5 2 == MkRem 2 1
  , findRemainder 5 3 == MkRem 1 2
  , findRemainder 5 4 == MkRem 1 1
  , findRemainder 5 5 == MkRem 1 0
  , findRemainder 5 6 == MkRem 0 5
  , findRemainder 5 7 == MkRem 0 5
  ]

testSnocVect : List Bool
testSnocVect =
  [ snocVect (the (Vect 0 Int) []) == EmptyV
  , snocVect [1] == SnocV 1 [] EmptyV
  , snocVect [1,2] == SnocV 2 [1] (SnocV 1 [] EmptyV)
  , snocVect [1,2,3] == SnocV 3 [1,2] (SnocV 2 [1] (SnocV 1 [] EmptyV))
  ]

testRotrightList : List Bool
testRotrightList =
  [ rotright [1,2,3] == [3,1,2]
  , rotright2 [1,2,3] == [2,3,1]

  , rotrightN 0 [1,2,3] == [1,2,3]
  , rotrightN 1 [1,2,3] == rotright [1,2,3]
  , rotrightN 2 [1,2,3] == rotright2 [1,2,3]
  , rotrightN 3 [1,2,3] == rotrightN 0 [1,2,3]
  , rotrightN 4 [1,2,3] == rotrightN 1 [1,2,3]
  , rotrightN 5 [1,2,3] == rotrightN 2 [1,2,3]
  , rotrightN 6 [1,2,3] == rotrightN 3 [1,2,3]

  , rotrightRec [1,2,3] == rotright [1,2,3]
  , rotright2Rec [1,2,3] == rotright2 [1,2,3]

  , rotrightNRec 0 [1,2,3] == rotrightN 0 [1,2,3]
  , rotrightNRec 1 [1,2,3] == rotrightN 1 [1,2,3]
  , rotrightNRec 2 [1,2,3] == rotrightN 2 [1,2,3]
  , rotrightNRec 3 [1,2,3] == [1,2,3]
  , rotrightNRec 4 [1,2,3] == rotrightNRec 1 [1,2,3]
  , rotrightNRec 5 [1,2,3] == rotrightNRec 2 [1,2,3]
  , rotrightNRec 6 [1,2,3] == rotrightNRec 3 [1,2,3]

  , rotrightNRec2 0 [1,2,3] == rotrightNRec 0 [1,2,3]
  , rotrightNRec2 1 [1,2,3] == rotrightNRec 1 [1,2,3]
  , rotrightNRec2 2 [1,2,3] == rotrightNRec 2 [1,2,3]
  , rotrightNRec2 3 [1,2,3] == rotrightNRec 3 [1,2,3]
  , rotrightNRec2 4 [1,2,3] == rotrightNRec 4 [1,2,3]
  , rotrightNRec2 5 [1,2,3] == rotrightNRec 5 [1,2,3]
  , rotrightNRec2 6 [1,2,3] == rotrightNRec 6 [1,2,3]

  , rotrightNRec3 0 [1,2,3] == rotrightNRec2 0 [1,2,3]
  , rotrightNRec3 1 [1,2,3] == rotrightNRec2 1 [1,2,3]
  , rotrightNRec3 2 [1,2,3] == rotrightNRec2 2 [1,2,3]
  , rotrightNRec3 3 [1,2,3] == rotrightNRec2 3 [1,2,3]
  , rotrightNRec3 4 [1,2,3] == rotrightNRec2 4 [1,2,3]
  , rotrightNRec3 5 [1,2,3] == rotrightNRec2 5 [1,2,3]
  , rotrightNRec3 6 [1,2,3] == rotrightNRec2 6 [1,2,3]
  ]

testRotrightVec : List Bool
testRotrightVec =
  [ rotrightVecNRec 0 [1,2,3] == [1,2,3]
  , rotrightVecNRec 1 [1,2,3] == [3,1,2]
  , rotrightVecNRec 2 [1,2,3] == [2,3,1]
  , rotrightVecNRec 3 [1,2,3] == [1,2,3]
  , rotrightVecNRec 4 [1,2,3] == rotrightVecNRec 1 [1,2,3]
  , rotrightVecNRec 5 [1,2,3] == rotrightVecNRec 2 [1,2,3]
  , rotrightVecNRec 6 [1,2,3] == rotrightVecNRec 3 [1,2,3]

  , rotrightVecNRec3 0 [1,2,3] == rotrightVecNRec 0 [1,2,3]
  , rotrightVecNRec3 1 [1,2,3] == rotrightVecNRec 1 [1,2,3]
  , rotrightVecNRec3 2 [1,2,3] == rotrightVecNRec 2 [1,2,3]
  , rotrightVecNRec3 3 [1,2,3] == rotrightVecNRec 3 [1,2,3]
  , rotrightVecNRec3 4 [1,2,3] == rotrightVecNRec 4 [1,2,3]
  , rotrightVecNRec3 5 [1,2,3] == rotrightVecNRec 5 [1,2,3]
  , rotrightVecNRec3 6 [1,2,3] == rotrightVecNRec 6 [1,2,3]
  ]

testRotleftList : List Bool
testRotleftList =
  [ rotleft [1,2,3] == [2,3,1]
  , rotleft2 [1,2,3] == [3,1,2]

  , rotleftN 0 [1,2,3] == [1,2,3]
  , rotleftN 1 [1,2,3] == rotleft [1,2,3]
  , rotleftN 2 [1,2,3] == rotleft2 [1,2,3]
  , rotleftN 3 [1,2,3] == rotleftN 0 [1,2,3]
  , rotleftN 4 [1,2,3] == rotleftN 1 [1,2,3]
  , rotleftN 5 [1,2,3] == rotleftN 2 [1,2,3]
  , rotleftN 6 [1,2,3] == rotleftN 3 [1,2,3]

  , rotleftRec [1,2,3] == rotleft [1,2,3]
  , rotleft2Rec [1,2,3] == rotleft2 [1,2,3]

  , rotleftNRec 0 [1,2,3] == rotleftN 0 [1,2,3]
  , rotleftNRec 1 [1,2,3] == rotleftN 1 [1,2,3]
  , rotleftNRec 2 [1,2,3] == rotleftN 2 [1,2,3]
  , rotleftNRec 3 [1,2,3] == [1,2,3]
  , rotleftNRec 4 [1,2,3] == rotleftNRec 1 [1,2,3]
  , rotleftNRec 5 [1,2,3] == rotleftNRec 2 [1,2,3]
  , rotleftNRec 6 [1,2,3] == rotleftNRec 3 [1,2,3]

  , rotleftNRec3 0 [1,2,3] == rotleftNRec 0 [1,2,3]
  , rotleftNRec3 1 [1,2,3] == rotleftNRec 1 [1,2,3]
  , rotleftNRec3 2 [1,2,3] == rotleftNRec 2 [1,2,3]
  , rotleftNRec3 3 [1,2,3] == rotleftNRec 3 [1,2,3]
  , rotleftNRec3 4 [1,2,3] == rotleftNRec 4 [1,2,3]
  , rotleftNRec3 5 [1,2,3] == rotleftNRec 5 [1,2,3]
  , rotleftNRec3 6 [1,2,3] == rotleftNRec 6 [1,2,3]
  ]

testRotleftVec : List Bool
testRotleftVec =
  [ rotleftVecNRec 0 [1,2,3] == [1,2,3]
  , rotleftVecNRec 1 [1,2,3] == [2,3,1]
  , rotleftVecNRec 2 [1,2,3] == [3,1,2]
  , rotleftVecNRec 3 [1,2,3] == [1,2,3]
  , rotleftVecNRec 4 [1,2,3] == rotleftVecNRec 1 [1,2,3]
  , rotleftVecNRec 5 [1,2,3] == rotleftVecNRec 2 [1,2,3]
  , rotleftVecNRec 6 [1,2,3] == rotleftVecNRec 3 [1,2,3]

  , rotleftVecNRec3 0 [1,2,3] == rotleftVecNRec 0 [1,2,3]
  , rotleftVecNRec3 1 [1,2,3] == rotleftVecNRec 1 [1,2,3]
  , rotleftVecNRec3 2 [1,2,3] == rotleftVecNRec 2 [1,2,3]
  , rotleftVecNRec3 3 [1,2,3] == rotleftVecNRec 3 [1,2,3]
  , rotleftVecNRec3 4 [1,2,3] == rotleftVecNRec 4 [1,2,3]
  , rotleftVecNRec3 5 [1,2,3] == rotleftVecNRec 5 [1,2,3]
  , rotleftVecNRec3 6 [1,2,3] == rotleftVecNRec 6 [1,2,3]
  ]

testJoinCons : List Bool
testJoinCons =
  [ consIn (consOut []) == the (List Int) []
  , consIn (consOut [1]) == [1]
  , consIn (consOut [1,2]) == [1,2]
  , consIn (consOut [1,2,3]) == [1,2,3]

  , consIn2 (consOut (the (List Int) [])) == []
  , consIn2 (consOut [1]) == [1]
  , consIn2 (consOut [1,2]) == [1,2]
  , consIn2 (consOut [1,2,3]) == [1,2,3]
  ]

testJoinSnoc : List Bool
testJoinSnoc =
  [ snocIn (snocOut SNil) == the (SnocL Int) SNil
  , snocIn (snocOut (SSnoc SNil 1)) == (SSnoc SNil 1)
  , snocIn (snocOut (SSnoc (SSnoc SNil 1) 2)) == (SSnoc (SSnoc SNil 1) 2)
  , snocIn (snocOut (SSnoc (SSnoc (SSnoc SNil 1) 2) 3)) == (SSnoc (SSnoc (SSnoc SNil 1) 2) 3)
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
  runTest "testRemainder" () checkBool testRemainder
  runTest "testSnocVect" () checkBool testSnocVect
  runTest "testRotrightList" () checkBool testRotrightList
  runTest "testRotrightVec" () checkBool testRotrightVec
  runTest "testRotleftList" () checkBool testRotleftList
  runTest "testRotleftVec" () checkBool testRotleftVec
  runTest "testJoinCons" () checkBool testJoinCons
  runTest "testJoinSnoc" () checkBool testJoinSnoc
