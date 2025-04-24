module Datastore

import Data.Vect

import Schema

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

export
search : (store : DataStore) -> (SchemaType (schema store) -> Bool) -> List (Nat, SchemaType (schema store))
search store p = go p 0 id (items store) []
  where
    -- Use composition for building results in index increasing order.
    go : (a -> Bool) -> Nat
          -> (List (Nat, a) -> List (Nat, a))
          -> Vect n a
          -> List (Nat, a) -> List (Nat, a)
    go _ _ zs []        = zs
    go p i zs (x :: xs) = go p (i + 1) (if p x then zs . ((i, x) ::) else zs) xs

searchV : DataStore -> {scm2 : Schema} -> (SchemaType scm2 -> Bool) -> List (Nat, SchemaType scm2)
--searchV store {scm2 = scm2} p =

export
setSchema : DataStore -> Schema -> Maybe DataStore
setSchema store scm = case size store of
                       Z => Just (MkData scm _ [])
                       S _ => Nothing

export
getEntry' : Integer -> (store : DataStore) -> Maybe (SchemaType (schema store))
getEntry' pos store = (\i => index i (items store)) <$> integerToFin pos (size store)

