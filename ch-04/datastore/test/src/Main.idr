module Main

import Data.String
import Data.List
import Data.Vect
import Datastore
import Cmd

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

runTest : List (String, String) -> Maybe (Nat, String)
runTest ts =
  let n = length ts
  in  case foldl go (Right (MkData _ [])) (zip [0..n] ts) of
           Left err => Just err
           Right _  => Nothing
  where
    go : Either (Nat, String) DataStore -> (Nat, (String, String)) -> Either (Nat, String) DataStore
    go err@(Left _) _ = err
    go (Right store) (n, (input, expected)) =
      case processInput store input of
           Just (got, store') =>
            let v = trim got
            in  if v == expected then Right store' else Left (n, v)
           Nothing => Left (n, "Nothing")

main : IO ()
main = case runTest testData of
            Nothing => putStrLn "Test successful!"
            Just err => putStrLn ("Test failed with " ++ show err ++ "\n")
