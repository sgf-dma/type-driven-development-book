module Main

import Data.String
import Data.List
import Data.Vect

import Schema
import Datastore
import Cmd
import TestUtils
import TestSchema
import TestDatastore
import TestCmd

runTest : Show b => (name : String) -> (acc0 : a) -> (run : a -> b -> Maybe a) -> List b -> IO ()
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
  runTest "Utils" () checkBool testUtilsData
  runTest "SchemaDisplay" () checkBool testSchemaParse
  runTest "SchemaParse" () checkBool testSchemaParse
  runTest "SchemaValue" () checkBool testSchemaValue
  runTest "SchemaSubtreesAll" () checkBool testSchemaSubtreesAll
  runTest "SchemaSubtrees" () checkBool testSchemaSubtrees
  runTest "SchemaMatcher" () checkBool testSchemaMatcher
  runTest "StoreSearch" () checkBool testStoreSearch
  runTest "Cmd" (MkData SString _ []) interactiveTest testCmd

