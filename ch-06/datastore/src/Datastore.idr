module Datastore

import Data.String
import Data.List1
import Data.Vect

export infixr 5 .+.

public export
data Schema = SString
            | SInt
            | (.+.) Schema Schema

export
displaySchema : Schema -> String
displaySchema SInt = "Int"
displaySchema SString = "String"
displaySchema ((.+.) s1 s2) = displaySchema s1 ++ " " ++ displaySchema s2

export
parseSchema : String -> Maybe Schema
parseSchema s = case parsePrefix s of
                     Nothing => Nothing
                     Just (s1, "") => Just s1
                     Just (s1, rest) => case parseSchema (ltrim rest) of
                                             Nothing => Nothing
                                             Just s2 => Just (s1 .+. s2)
  where
    parsePrefix : String -> Maybe (Schema, String)
    parsePrefix input =
      case span (/= ' ') input of
           ("String", rest) => Just (SString, rest)
           ("Int", rest) => Just (SInt, rest)
           _ => Nothing

public export
TypeSchema : Type -> Maybe Schema
TypeSchema Int = Just SInt
TypeSchema String = Just SString
TypeSchema (a, b) = (.+.) <$> TypeSchema a <*> TypeSchema b
TypeSchema _ = Nothing

public export
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (a .+. b) = (SchemaType a, SchemaType b)

export
display : {scm : Schema} -> SchemaType scm -> String
display {scm = SInt} x = show x
display {scm = SString} x = show x
display {scm = (.+.) a b} (x, y) = "(" ++ display x ++ ", " ++ display y ++ ")"

parsePrefix : (scm : Schema) -> String -> Maybe (SchemaType scm, String)
parsePrefix SInt input =
  case span isDigit input of
       ("", _) => Nothing
       (s, rest) => Just (cast s, ltrim rest)
parsePrefix SString input = getQuoted (unpack input)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: rs) = 
       case span (/= '"') rs of
            (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
            _ => Nothing
    getQuoted _ = Nothing
parsePrefix ((.+.) a b) input =
  case parsePrefix a input of
       Nothing => Nothing
       Just (left, rr) => case parsePrefix b rr of
                               Nothing => Nothing
                               Just (right, rest) => Just ((left, right), rest)

-- parsePrefix' requires one or more spaces between elements. Also, as a
-- side-effect, it leaves trailing spaces as is. Thus, to use it, i need to
-- remove trailing spaces in parseBySchema.
parsePrefix' : (scm : Schema) -> String -> Maybe (SchemaType scm, String)
parsePrefix' SInt input =
  case span isDigit input of
       ("", _) => Nothing
       (s, rest) => Just (cast s, rest)
parsePrefix' SString input =
  case strM input of
       StrCons '"' rs => let (val, rs') = span (/= '"') rs
                         in  case strM rs' of
                                  StrCons _ rest => Just (val, rest)
                                  _  => Nothing
       _ => Nothing
parsePrefix' ((.+.) a b) input =
  case parsePrefix' a input of
       Nothing => Nothing
       Just (left, rr) => case span (== ' ') rr of
                               (_, "") => Nothing
                               ("", _) => Nothing
                               (l, rr') => case parsePrefix' b (ltrim rr') of
                                                Nothing => Nothing
                                                Just (right, rest) => Just ((left, right), rest)

export
parseBySchema : (scm : Schema) -> String -> Maybe (SchemaType scm)
parseBySchema scm input =
  case parsePrefix scm input of
       Just (res, "") => Just res
       _ => Nothing

public export
record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items: Vect size (SchemaType schema)

--size : DataStore -> Nat
--size (MkData _ n _) = n

--schema : DataStore -> Schema
--schema (MkData scm _ _) = scm

--items : (store : DataStore) -> Vect (size store) (SchemaType (schema store))
--items (MkData schema _ xs) = xs
-- Or i can use dependent pairs, but do i really need such function?
items' : (store : DataStore) -> (scm ** Vect (size store) (SchemaType scm))
items' (MkData scm _ xs) = (scm ** xs)

export
addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData scm m xs) y = MkData _ _ (add' xs) -- MkData _ _ (snoc xs y)
  where
    add' : Vect n (SchemaType scm) -> Vect (S n) (SchemaType scm)
    add' [] = [y]
    add' (x :: xs) = x :: add' xs

{-
export
search : (String -> Bool) -> DataStore -> List (Nat, String)
search p store = go p 0 id (items store) []
  where
    -- Use composition for building results in index increasing order.
    go : (a -> Bool) -> Nat
          -> (List (Nat, a) -> List (Nat, a))
          -> Vect n a
          -> List (Nat, a) -> List (Nat, a)
    go _ _ zs []        = zs
    go p i zs (x :: xs) = go p (i + 1) (if p x then zs . ((i, x) ::) else zs) xs

-}

export
setSchema : DataStore -> Schema -> Maybe DataStore
setSchema store scm = case size store of
                       Z => Just (MkData scm _ [])
                       S _ => Nothing

export
getEntry' : Integer -> (store : DataStore) -> Maybe (SchemaType (schema store))
getEntry' pos store = (\i => index i (items store)) <$> integerToFin pos (size store)

