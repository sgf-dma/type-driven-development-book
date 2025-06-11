
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
  GetAll : Command scm
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

parseCommand : {scm : Schema} -> String -> String -> Either String (Command scm)
parseCommand "schema" args = maybe (Left "Failed to parse schema") Right $ do
  (scm, "") <- parseSchemaPrefix args | _ => Nothing
  pure (SetSchema scm)
parseCommand "add" args =
  maybe (Left ("Failed to parse new value for schema " ++ displaySchema True scm)) Right $ do
    (val, "") <- parsePrefix False scm args | _ => Nothing
    pure (Add val)
parseCommand "get" args =
  case span isDigit args of
       ("", "") => pure GetAll
       (nstr, "") => pure (Get (cast nstr))
       _ => Left "Bad element number"
parseCommand "size" "" = pure Size
parseCommand "search" args = maybe (Left "Failed to parse search query") Right $ do
  (scm, rest) <- parseSchemaPrefix args
  (val, "") <- parsePrefix True scm rest | _ => Nothing
  pure (Search scm val)
parseCommand "quit" "" = pure Quit
parseCommand _ _ = Left "Valid commands are 'schema', 'add', 'get', 'size', 'search', 'quit'\n"

export
parse : (scm : Schema) -> String -> Either String (Command scm)
parse _ input =
  let (cmd, args) = span (/= ' ') input
  in  parseCommand cmd (ltrim args)

export
processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
  = case parse (schema store) input of
         Left err => Just ("Error: " ++ err ++ "\n", store)
         Right (SetSchema scm') =>
            case setSchema store scm' of
                 Nothing => Just ("Can't update schema\n", store)
                 Just store' => Just ("Updated to schema " ++ displaySchema True scm' ++ "\n", store')
         Right (Add item) =>
            Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
         Right GetAll => Just (displayResult (getAllEntries store), store)
         Right (Get pos) =>
            case getEntry pos store of
                Nothing => Just ("Out of range \n", store)
                Just val => Just (display val ++ "\n", store)
         Right Size => Just (show (size store) ++ "\n", store)
         Right (Search scm' val) =>
            Just (displayResult (searchWith store [] scm' val), store)
         Right Quit => Nothing
  where
    displayResult : List (Nat, SchemaType (schema store)) -> String
    displayResult = foldr (++) "\n" . intersperse "\n" . map showResult
      where
        showResult : (Nat, SchemaType (schema store)) -> String
        showResult (n, x) = "(" ++ show n ++ ", " ++ display x ++ ")"

