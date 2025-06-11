
module Cmd2

import Data.Vect
import Data.String

import Schema
import Cmd
import Datastore2

export
partial processInput2 : (scm ** DataStore2 scm) -> String -> Maybe (String, (scm' ** DataStore2 scm'))
processInput2 (scm ** store) input
  = case parse scm input of
         Left err => Just ("Error: " ++ err ++ "\n", (_ ** store))
         Right (Add item) =>
            Just ("ID " ++ show (size store) ++ "\n", (_ ** addToStore2 store item))
         Right GetAll => Just (displayResult (getAllEntries store), (_ ** store))
         Right (Get pos) => case getEntry2 pos store of
                                Nothing => Just ("Out of range \n", (_ ** store))
                                Just val => Just (display val, (_ ** store))
         Right Size => Just (show (size store) ++ "\n", (_ ** store))
         Right (Search scm' str) => ?cs -- Just (show (search (isInfixOf str) store) ++ "\n", store)
         Right Quit => Nothing
         Right (SetSchema scm') =>
              case setSchema2 store scm' of
                   Nothing => Just ("Can't update schema\n", (_ ** store))
                   Just store' => Just ("Updated to schema " ++ displaySchema True scm' ++ "\n", (_ ** store'))
  where
    displayResult : List (Nat, SchemaType scm) -> String
    displayResult = foldr (++) "\n" . intersperse "\n" . map showResult
      where
        showResult : (Nat, SchemaType scm) -> String
        showResult (n, x) = "(" ++ show n ++ ", " ++ display x ++ ")"

