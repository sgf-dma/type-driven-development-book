module Main

import Data.List
import Lib

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

  , rotleftRec [1,2,3] == rotleft [1,2,3]
  , rotleft2Rec [1,2,3] == rotleft2 [1,2,3]
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
