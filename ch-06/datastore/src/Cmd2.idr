
module Cmd2

import Datastore
import Cmd
import Datastore2
import Data.Vect
import Data.String

getEntry2 : Integer -> {scm : Schema} -> DataStore2 scm -> Maybe (String, DataStore2 scm)
getEntry2 pos store =
  case integerToFin pos (size store) of
       Nothing => Just ("Out of range\n", store)
       Just idx => Just (display (index idx (items store)) ++ "\n", store)

export
partial processInput2 : (scm ** DataStore2 scm) -> String -> Maybe (String, (scm' ** DataStore2 scm'))
processInput2 (scm ** store) input
  = case parse scm input of
         Nothing => Just ("Invalid command\n", (_ ** store))
         Just (Add item) =>
            Just ("ID " ++ show (size store) ++ "\n", (_ ** addToStore2 store item))
         Just (Get pos) => case getEntry2' pos store of
                                Nothing => Just ("Out of range\n", (_ ** store))
                                Just item => Just (display item ++ "\n", (_ ** store))
         Just Size => Just (show (size store) ++ "\n", (_ ** store))
         Just (Search str) => ?cs -- Just (show (search (isInfixOf str) store) ++ "\n", store)
         Just Quit => Nothing
         Just (SetSchema scm') =>
              case setSchema2 store scm' of
                   Nothing => Just ("Can't update schema\n", (_ ** store))
                   Just store' => Just ("Updated to schema " ++ displaySchema scm' ++ "\n", (_ ** store'))

