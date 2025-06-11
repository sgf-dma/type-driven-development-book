module Datastore

import Data.String
import Data.Vect

import Schema

-- TODO: Implement Eq for DataStore. Embed Eq constraint on
-- (SchemaType schema) inside datatype.

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

-- The most basic search. Don't use it.
export
search' : (store : DataStore) -> (SchemaType (schema store) -> Bool) -> List (Nat, SchemaType (schema store))
search' store p = foldr (go p) (const id) (items store) 0 []
  where
    -- Use composition for building results in index increasing order.
    go : (p : a -> Bool)
          -> (x : a)
          -> (zs : Nat -> List (Nat, a) -> List (Nat, a))
          -> (i : Nat) -> List (Nat, a) -> List (Nat, a)
    go p x zs i = if p x then zs (i + 1) . ((i, x) ::) else zs (i + 1)

-- Search datastore for elements, on which predicate p for particular
-- sub-Schema, returns True.
export
search : (store : DataStore) -> (scm : Schema) -> (p : SchemaType scm -> Bool) -> List (Nat, SchemaType (schema store))
search store scm p = foldr go (const []) (items store) 0
  where
    go : SchemaType (schema store)
       -> (Nat -> List (Nat, SchemaType (schema store)))
       ->  Nat -> List (Nat, SchemaType (schema store))
    go v acc i =
      let match = any p . findSubtreeValues (schema store) scm
      in  if match v
             then (i, v) :: acc (i + 1)
             else acc (i + 1)

-- TODO: Implement polymorphic 'search' over different DataStore
-- implementations.

-- Search datastore for elements, on which predicate, built from a list of
-- Schema comparision functions, returns True.
export
searchWith
      : (store : DataStore)
      -> List (scm' : Schema ** SchemaType scm' -> SchemaType scm' -> Bool)
      -> (scm : Schema)
      -> SchemaType scm
      -> List (Nat, SchemaType (schema store))
searchWith store funcs scm val =
  let cmp = buildMatcher scm val funcs
  in  search store scm cmp

export
setSchema : DataStore -> Schema -> Maybe DataStore
setSchema store scm = case size store of
                       Z => Just (MkData scm _ [])
                       S _ => Nothing

export
getEntry : Integer -> (store : DataStore) -> Maybe (SchemaType (schema store))
getEntry pos store = (\i => index i (items store)) <$> integerToFin pos (size store)

export
getAllEntries : (store : DataStore) -> List (Nat, SchemaType (schema store))
getAllEntries store = foldr go (const []) (items store) 0
  where
    go : (x : SchemaType (schema store))
       -> (acc : Nat -> List (Nat, SchemaType (schema store)))
       -> (i : Nat) -> List (Nat, SchemaType (schema store))
    go x acc i = (i, x) :: acc (i + 1)

