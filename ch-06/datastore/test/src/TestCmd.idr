
module TestCmd

import Data.String
import Data.Vect

import Schema
import Datastore
import Cmd
import Cmd2

-- For use with 'interactiveTest'.
export
testCmd : List (String, String)
testCmd =
  [ ("schema Int (Int String)", "Updated to schema (Int (Int String))")
  , ("add 3", "Error: Failed to parse new value for schema (Int (Int String))")

  -- 2-5
  , ("add (1 (2 \"abc\"))", "ID 0")
  , ("get 0", "(1, (2, \"abc\"))")
  , ("add 2 3 \"dbf\"", "ID 1")
  , ("get 1", "(2, (3, \"dbf\"))")

  -- 6-
  , ("search Int 2", "(0, (1, (2, \"abc\")))\n(1, (2, (3, \"dbf\")))")
  , ("search String \"b\"", "(0, (1, (2, \"abc\")))\n(1, (2, (3, \"dbf\")))")
  , ("search String \"a\"", "(0, (1, (2, \"abc\")))")

  -- 9-12
  , ("search (Int String) (2 \"b\")", "(0, (1, (2, \"abc\")))")
  , ("search (Int String) (3 \"b\")", "(1, (2, (3, \"dbf\")))")
  , ("search (Int String) (3 \"db\")", "(1, (2, (3, \"dbf\")))")
  , ("search (Int String) (2 \"db\")", "")

  -- 13-
  , ("size", "2")
  ]
