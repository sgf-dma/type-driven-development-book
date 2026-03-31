module Main

import Data.String
import Data.List
import Data.Vect
import Data.Either

import Schema
import Datastore
import Datastore2
import Cmd
import Cmd2
import TestUtils
import TestSchema
import TestDatastore
import TestCmd


runTest : Show b => (name : String) -> (acc0 : a) -> (run : a -> b -> Either String a) -> List b -> IO ()
runTest name acc0 run ts =
    let n = length ts
    in  either
          (\err => putStrLn ("Test '" ++ name ++ "' failed: " ++ show err))
          (\_   => putStrLn ("Test '" ++ name ++ "' successful!"))
          $ foldl go (Right acc0) (zip [0..n] ts)
  where
    go : Either (Nat, String) a -> (Nat, b) -> Either (Nat, String) a
    go err@(Left _) _ = err
    go (Right acc) (n, v) =
      case run acc v of
           Left err => Left (n, show v ++ " with err: " ++ err)
           Right acc' => Right acc'

interactiveTest : DataStore -> (String, String) -> Either String DataStore
interactiveTest store (input, expected) = do
      (res, store') <- maybeToEither "processInput failed" (processInput store input)
      let got = trim res
      if got == expected then pure store' else Left ("got " ++ got)

checkBool : a -> Bool -> Either String a
checkBool _ False = Left ""
checkBool v True = Right v

interactiveTest2 : (scm : Schema ** DataStore2 scm) ->
                   (String, String) -> Either String (scm' : Schema ** DataStore2 scm')
interactiveTest2 (scm ** store) (input, expected) = do
      (res, (scm' ** store')) <- maybeToEither "processInput2 failed" (processInput2 (scm ** store) input)
      let got = trim res
      if got == expected then pure (scm' ** store') else Left ("got " ++ got)

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
  runTest "Cmd2" (SString .+. SString .+. SInt ** empty2) interactiveTest2 testCmd

