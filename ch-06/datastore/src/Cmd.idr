
module Cmd

import Data.Vect
import Data.String

import Schema
import Datastore

public export
data Command : Schema -> Type where
  Add : SchemaType scm -> Command scm
  Get : Integer -> Command scm
  Size : Command scm
  Search : (scm' : Schema) -> SchemaType scm' -> Command scm
  Quit : Command scm
  SetSchema : Schema -> Command scm

data Command' : Type -> Type where
  Add' : SchemaType scm -> Command' (SchemaType scm)
  Get' : Integer -> Command' (SchemaType scm)
  Size' : Command' (SchemaType scm)
  Search' : SchemaType scm -> Command' (SchemaType scm)
  Quit' : Command' (SchemaType scm)

parseCommand : {scm : Schema} -> String -> String -> Maybe (Command scm)
parseCommand "schema" args = do
  (scm, "") <- parseSchemaPrefix args | _ => Nothing
  pure (SetSchema scm)
parseCommand "add" args = do
  (val, "") <- parsePrefix scm args | _ => Nothing
  pure (Add val)
parseCommand "get" args = if all isDigit (unpack args)
                             then Just (Get (cast args))
                             else Nothing
parseCommand "size" "" = Just Size
parseCommand "search" args = do
  (scm, rest) <- parseSchemaPrefix args
  (val, "") <- parsePrefix scm rest | _ => Nothing
  pure (Search scm val)
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
         Just (SetSchema scm') =>
              case setSchema store scm' of
                   Nothing => Just ("Can't update schema\n", store)
                   Just store' => Just ("Updated to schema " ++ displaySchema True scm' ++ "\n", store')
         Just (Add item) =>
            Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
         Just (Get pos) => getEntry pos store
         Just Size => Just (show (size store) ++ "\n", store)
         Just (Search scm' val) => Just (displayResult (search store scm' (const True)) ++ "\n", store)
         Just Quit => Nothing
  where
    displayResult : List (Nat, SchemaType (schema store)) -> String
    displayResult [] = ""
    displayResult ((n, x) :: xs) = "\n(" ++ show n ++ ", " ++ display x ++ ")" ++ displayResult xs

