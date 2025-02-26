
module Cmd

import Datastore
import Data.Vect
import Data.String

data Command = Add String
             | Get Integer
             | Size
             | Search String
             | Quit

parseCommand : String -> String -> Maybe Command
parseCommand "add" args = Just (Add args)
parseCommand "get" args = if all isDigit (unpack args)
                             then Just (Get (cast args))
                             else Nothing
parseCommand "size" "" = Just Size
parseCommand "search" args = Just (Search args)
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

parse : String -> Maybe Command
parse input = let (cmd, args) = span (/= ' ') input
              in  parseCommand cmd (ltrim args)

getEntry : Integer -> DataStore -> Maybe (String, DataStore)
getEntry pos store =
  case integerToFin pos (size store) of
       Nothing => Just ("Out of range\n", store)
       Just idx => Just (index idx (items store) ++ "\n", store)

export
processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
  = case parse input of
         Nothing => Just ("Invalid command\n", store)
         Just (Add item) =>
            Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
         Just (Get pos) => getEntry pos store
            --(\idx => (index idx (items store), store)) <$> natToFin (cast pos) (size store)
            {-
            case integerToFin pos (size store) of
                 Just idx => Just (index idx (items store) ++ "\n", store)
                 Nothing => Just ("Out of range\n", store)
                 -}
         Just Size => Just (show (size store) ++ "\n", store)
         Just (Search str) => Just (show (search (isInfixOf str) store) ++ "\n", store)
         Just Quit => Nothing
