
module Cmd

import Datastore
import Data.Vect
import Data.String

public export
data Command : Schema -> Type where
  Add : SchemaType scm -> Command scm
  Get : Integer -> Command scm
  Size : Command scm
  Search : SchemaType scm -> Command scm
  Quit : Command scm
  SetSchema : Schema -> Command scm

data Command' : Type -> Type where
  Add' : SchemaType scm -> Command' (SchemaType scm)
  Get' : Integer -> Command' (SchemaType scm)
  Size' : Command' (SchemaType scm)
  Search' : SchemaType scm -> Command' (SchemaType scm)
  Quit' : Command' (SchemaType scm)

parseCommand : {scm : Schema} -> String -> String -> Maybe (Command scm)
parseCommand "schema" args = case parseSchema args of
                               Nothing => Nothing
                               Just scm => Just (SetSchema scm)
parseCommand "add" args = case parseBySchema scm args of 
                               Nothing => Nothing
                               Just val => Just (Add val)
parseCommand "get" args = if all isDigit (unpack args)
                             then Just (Get (cast args))
                             else Nothing
parseCommand "size" "" = Just Size
--parseCommand "search" args = Just (Search args)
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

export
parse : (scm : Schema) -> String -> Maybe (Command scm)
parse _ input =
  let (cmd, args) = span (/= ' ') input
  in  parseCommand cmd (ltrim args)

getEntry : Integer -> DataStore -> Maybe (String, DataStore)
getEntry pos store =
  case integerToFin pos (size store) of
       Nothing => Just ("Out of range\n", store)
       Just idx => Just (display (index idx (items store)) ++ "\n", store)

export
processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
  = case parse (schema store) input of
         Nothing => Just ("Invalid command\n", store)
         Just (Add item) =>
            Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
         Just (Get pos) => getEntry pos store
         Just Size => Just (show (size store) ++ "\n", store)
         Just (Search str) => ?cs -- Just (show (search (isInfixOf str) store) ++ "\n", store)
         Just Quit => Nothing
         Just (SetSchema scm) =>
              case setSchema store scm of
                   Nothing => Just ("Can't update schema\n", store)
                   Just store' => Just ("Updated to schema " ++ displaySchema scm ++ "\n", store')
