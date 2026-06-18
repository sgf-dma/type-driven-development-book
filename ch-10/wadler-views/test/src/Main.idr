module Main

import Data.Nat
import Data.Vect
import Data.List

import Remainder
import SnocVect
import Ch5
import Ch6
import Ch7
import Ch8
import Ch9
import Ch12

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

testZipView : List Bool
testZipView =
  [ zipView (the (List (Int, Int)) []) == ZPair [] []
  , zipView [(1, 2)] == ZPair [1] [2]
  , zipView [(1, 2), (3, 4)] == ZPair [1,3] [2,4]
  , zipView [(1, 2), (3, 4), (5, 6)] == ZPair [1,3,5] [2,4,6]
  ]

testZipVecView : List Bool
testZipVecView =
  [ zipVecView (the (Vect 0 (Int, Int)) []) == ZVecPair [] []
  , zipVecView [(1, 2)] == ZVecPair [1] [2]
  , zipVecView [(1, 2), (3, 4)] == ZVecPair [1,3] [2,4]
  , zipVecView [(1, 2), (3, 4), (5, 6)] == ZVecPair [1,3,5] [2,4,6]
  ]

tree1 : Tree String
tree1 = Branch (Branch (Leaf "f") (Leaf "a")) (Leaf "b")

tree2 : Tree String
tree2 = Branch (Leaf "f") (Leaf "a")

tree3 : Tree String
tree3 = Branch (Leaf "f") (Branch (Leaf "a") (Leaf "b"))

tree4 : Tree String
tree4 = Branch (Branch (Branch (Leaf "f") (Leaf "a")) (Branch (Leaf "c") (Leaf "d"))) (Leaf "b")

testTrees : List Bool
testTrees =
  [
    spineToTree (treeToSpine tree1) == tree1
  , spineToTree (treeToSpine tree2) == tree2
  , spineToTree (treeToSpine tree3) == tree3
  , spineToTree (treeToSpine tree4) == tree4

  , spineToTree4' (treeToSpine4 tree1) == tree1
  , spineToTree4' (treeToSpine4 tree2) == tree2
  , spineToTree4' (treeToSpine4 tree3) == tree3
  , spineToTree4' (treeToSpine4 tree4) == tree4

  , spineToTree4 (treeToSpine4 tree1) == tree1
  , spineToTree4 (treeToSpine4 tree2) == tree2
  , spineToTree4 (treeToSpine4 tree3) == tree3
  , spineToTree4 (treeToSpine4 tree4) == tree4

  , spineTree4_1 (treeToSpine4 tree1) == treeToSpine tree1
  , spineTree4_1 (treeToSpine4 tree2) == treeToSpine tree2
  , spineTree4_1 (treeToSpine4 tree3) == treeToSpine tree3
  , spineTree4_1 (treeToSpine4 tree4) == treeToSpine tree4

  , fst (spineTree1_4 (treeToSpine tree1)) == tree1
  , fst (spineTree1_4 (treeToSpine tree2)) == tree2
  , fst (spineTree1_4 (treeToSpine tree3)) == tree3
  , fst (spineTree1_4 (treeToSpine tree4)) == tree4

  -- I don't need to check snd, like
  --    snd (spineTree1_4 (treeToSpine tree1)) == treeToSpine4 tree1
  -- first, because it won't work, because it needs decidable equality.
  -- Second, dependent pair (returned by spineTree1_4) guarantees, that Spine4 in
  -- second element matches to Tree in the first and my Eq instance for Spine4
  -- tells, that if types are equal, values are also equal. So, by comparing
  -- first element with reference Tree, i check whether types are equal. And
  -- there's no need to also check the values.
  ]

testParity : List Bool
testParity =
  [ parity 0 == Even
  , parity 1 == Odd
  , parity 2 == Even {k = 1}
  , parity 3 == Odd {k = 1}
  , parity 4 == Even {k = 2}
  , parity 5 == Odd {k = 2}

  , parity2 0 == Even
  , parity2 1 == Odd
  , parity2 2 == Even {k = 1}
  , parity2 3 == Odd {k = 1}
  , parity2 4 == Even {k = 2}
  , parity2 5 == Odd {k = 2}
  ]

testFib : List Bool
testFib =
  [ fibVc 0 == 0
  , fibVc 1 == 1
  , fibVc 2 == 1
  , fibVc 3 == 2
  , fibVc 4 == 3
  , fibVc 9 == 34

  , fibx 0 1 0 == 0
  , fibx 0 1 1 == 1
  , fibx 0 1 2 == 1
  , fibx 0 1 3 == 2
  , fibx 0 1 4 == 3
  , fibx 0 1 9 == 34

  , fibxVc 0 1 0 == 0
  , fibxVc 0 1 1 == 1
  , fibxVc 0 1 2 == 1
  , fibxVc 0 1 3 == 2
  , fibxVc 0 1 4 == 3
  , fibxVc 0 1 9 == 34

  , fibxVc2 0 1 0 == 0
  , fibxVc2 0 1 1 == 1
  , fibxVc2 0 1 2 == 1
  , fibxVc2 0 1 3 == 2
  , fibxVc2 0 1 4 == 3
  , fibxVc2 0 1 9 == 34

  , fibxVc2L 0 1 0 == 0
  , fibxVc2L 0 1 1 == 1
  , fibxVc2L 0 1 2 == 1
  , fibxVc2L 0 1 3 == 2
  , fibxVc2L 0 1 4 == 3
  , fibxVc2L 0 1 9 == 34
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
  runTest "testZipView" () checkBool testZipView
  runTest "testZipVecView" () checkBool testZipVecView
  runTest "testTrees" () checkBool testTrees
  runTest "testParity" () checkBool testParity
  runTest "testFib" () checkBool testFib
