
module Cmd

import Data.List
import Data.Vect
import Data.String

import Schema
import Datastore

-- Command is parametrized by Schema to make it clear, that all commands
-- are for values of certain schema, thus avoiding schema equality checks in
-- processInput (e.g. when adding an item to store, 'Add' command already have
-- a value of correct schema, which may be supplied to addToStore directly,
-- without any conversions or checks).
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
  (val, "") <- parsePrefix False scm args | _ => Nothing
  pure (Add val)
parseCommand "get" args = if all isDigit (unpack args)
                             then Just (Get (cast args))
                             else Nothing
parseCommand "size" "" = Just Size
parseCommand "search" args = do
  (scm, rest) <- parseSchemaPrefix args
  (val, "") <- parsePrefix True scm rest | _ => Nothing
  pure (Search scm val)
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

export
parse : (scm : Schema) -> String -> Maybe (Command scm)
parse _ input =
  let (cmd, args) = span (/= ' ') input
  in  parseCommand cmd (ltrim args)

export
processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
  = case parse (schema store) input of
         Nothing => Just ("Invalid command\n"
                          ++ "Valid commands are 'schema', 'add', 'get', 'size', 'search', 'quit'\n"
                         , store)
         Just (SetSchema scm') =>
              case setSchema store scm' of
                   Nothing => Just ("Can't update schema\n", store)
                   Just store' => Just ("Updated to schema " ++ displaySchema True scm' ++ "\n", store')
         Just (Add item) =>
              Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
         Just (Get pos) => case getEntry pos store of
                                Nothing => Just ("Out of range \n", store)
                                Just val => Just (display val ++ "\n", store)
         Just Size => Just (show (size store) ++ "\n", store)
         Just (Search scm' val) =>
              Just (displayResult (searchWith store [] scm' val), store)
         Just Quit => Nothing
  where
    displayResult : List (Nat, SchemaType (schema store)) -> String
    displayResult = foldr (++) "\n" . intersperse "\n" . map showResult
      where
        showResult : (Nat, SchemaType (schema store)) -> String
        showResult (n, x) = "(" ++ show n ++ ", " ++ display x ++ ")"

