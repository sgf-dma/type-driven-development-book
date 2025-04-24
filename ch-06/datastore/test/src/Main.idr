module Main

import Data.String
import Data.List
import Data.Vect

import Schema
import Datastore
import Cmd
import TestUtils
import TestSchema

testData : List (String, String)
testData   =
  [ ("add Shearer", "ID 0")
  , ("get 0", "Shearer")
  , ("add Milburn", "ID 1")
  , ("get 1", "Milburn")
  , ("add White", "ID 2")
  , ("get 2", "White")
  , ("size", "3")
  , ("search Mil", "[(1, \"Milburn\")]")
  , ("search i", "[(1, \"Milburn\"), (2, \"White\")]")
  , ("search abc", "[]")
  ]

runTest : Show b => (name : String) -> (acc0 : a) -> (p : a -> b -> Maybe a) -> List b -> IO ()
runTest name acc0 p ts =
    let n = length ts
    in  either
          (\err => putStrLn ("Test '" ++ name ++ "' failed with " ++ show err))
          (\_   => putStrLn ("Test '" ++ name ++ "' successful!"))
          $ foldl go (Right acc0) (zip [0..n] ts)
  where
    go : Either (Nat, String) a -> (Nat, b) -> Either (Nat, String) a
    go err@(Left _) _ = err
    go (Right acc) (n, v) =
      case p acc v of
           Nothing => Left (n, show v)
           Just acc' => Right acc'

interactiveTest : DataStore -> (String, String) -> Maybe DataStore
interactiveTest store (input, expected) = do
      (res, store') <- processInput store input
      let got = trim res
      if got == expected then pure store' else Nothing

checkBool : a -> Bool -> Maybe a
checkBool _ False = Nothing
checkBool v True = Just v

main : IO ()
main = do
  runTest "DataStore" (MkData SString _ []) interactiveTest testData
  runTest "Utils" () checkBool testUtilsData
  runTest "AllSubtrees" () checkBool testAllSubtrees
  runTest "Subtrees" () checkBool testSubtrees

