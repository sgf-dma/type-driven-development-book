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
search' : (store : DataStore) -> (SchemaType (schema store) -> Bool) -> List (Nat, SchemaType (schema store))
search' store p = foldr (go p) (const id) (items store) 0 []
  where
    -- Use composition for building results in index increasing order.
    go : (p : a -> Bool)
          -> (x : a)
          -> (zs : Nat -> List (Nat, a) -> List (Nat, a))
          -> (i : Nat) -> List (Nat, a) -> List (Nat, a)
    go p x zs i = if p x then zs (i + 1) . ((i, x) ::) else zs (i + 1)

export
-- Search in datastore elements with Schema scm2 on which predicate p returns True.
search : (store : DataStore) -> (scm2 : Schema) -> (p : SchemaType scm2 -> Bool) -> List (Nat, SchemaType (schema store))
search store scm2 p = foldr go (const []) (items store) 0
  where
    go : SchemaType (schema store)
       -> (Nat -> List (Nat, SchemaType (schema store)))
       ->  Nat -> List (Nat, SchemaType (schema store))
    go v acc i =
      let match = any p . findSubtreeValues (schema store) scm2
      in  if match v
             then (i, v) :: acc (i + 1)
             else acc (i + 1)

export
setSchema : DataStore -> Schema -> Maybe DataStore
setSchema store scm = case size store of
                       Z => Just (MkData scm _ [])
                       S _ => Nothing

export
getEntry' : Integer -> (store : DataStore) -> Maybe (SchemaType (schema store))
getEntry' pos store = (\i => index i (items store)) <$> integerToFin pos (size store)

