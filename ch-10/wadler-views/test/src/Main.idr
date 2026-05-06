module Main

import Data.Nat
import Data.List

import Lib
import Remainder

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

testSnocList : List Bool
testSnocList =
  [ rotright [1,2,3] == [3,1,2]

  , rotrightN 0 [1,2,3] == [1,2,3]
  , rotrightN 1 [1,2,3] == rotright [1,2,3]
  , rotrightN 2 [1,2,3] == rotright2 [1,2,3]
  , rotrightN 3 [1,2,3] == [1,2,3]
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

  , rotleft [1,2,3] == [2,3,1]
  , rotleft2 [1,2,3] == [3,1,2]
  , rotleft (rotleft [1,2,3]) == rotleft2 [1,2,3]

  , rotleftN 0 [1,2,3] == [1,2,3]
  , rotleftN 1 [1,2,3] == [2,3,1]
  , rotleftN 2 [1,2,3] == [3,1,2]
  , rotleftN 3 [1,2,3] == [1,2,3]

  -- , rotleftRec [1,2,3] == rotleft [1,2,3]
  -- , rotleft2Rec [1,2,3] == rotleft2 [1,2,3]
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
  runTest "testSnocList" () checkBool testSnocList
  runTest "testRemainder" () checkBool testRemainder
