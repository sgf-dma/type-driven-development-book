
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
         Nothing => Just ("Invalid command\n", (_ ** store))
         Just (Add item) =>
            Just ("ID " ++ show (size store) ++ "\n", (_ ** addToStore2 store item))
         Just (Get pos) => case getEntry2 pos store of
                                Nothing => Just ("Out of range \n", (_ ** store))
                                Just val => Just (display val, (_ ** store))
         Just Size => Just (show (size store) ++ "\n", (_ ** store))
         Just (Search scm' str) => ?cs -- Just (show (search (isInfixOf str) store) ++ "\n", store)
         Just Quit => Nothing
         Just (SetSchema scm') =>
              case setSchema2 store scm' of
                   Nothing => Just ("Can't update schema\n", (_ ** store))
                   Just store' => Just ("Updated to schema " ++ displaySchema True scm' ++ "\n", (_ ** store'))

