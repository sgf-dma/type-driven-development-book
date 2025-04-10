module Datastore2

import Data.Vect

import Schema

{-
public export
data DataStore2 : Type -> Type where
  MkData2 : (schema2 : Schema) -> (n : Nat) -> Vect n (SchemaType schema2) -> DataStore2 (SchemaType schema2)

schema2 : DataStore2 t -> Schema
schema2 (MkData2 scm _ _) = scm

-- But i can't implement this, because conversion from type back to Schema may
-- not work (see TypeSchema).
--schema2' : {1 scm : Schema} -> DataStore2 (SchemaType scm) -> Schema
--schema2' _ = scm

size2 : DataStore2 t -> Nat
size2 (MkData2 _ n _) = n

-- Though, in this case, where schema is seen in datastore's type, such
-- definition of DataStore does not make sense in the first place.
-}

public export
record DataStore2 (scm : Schema) where
  constructor MkData2
  size : Nat
  items : Vect size (SchemaType scm)

schema2 : {1 scm : Schema} -> DataStore2 scm -> Schema
schema2 _ = scm

export
addToStore2 : DataStore2 scm -> SchemaType scm -> DataStore2 scm
addToStore2 (MkData2 n xs) y = MkData2 _ (snoc xs y)

export
setSchema2 : DataStore2 scm -> (scm2 : Schema) -> Maybe (DataStore2 scm2)
setSchema2 store scm = case size store of
                       Z => Just (MkData2 _ [])
                       S _ => Nothing

export
getEntry2' : Integer -> {scm : Schema} -> DataStore2 scm -> Maybe (SchemaType scm)
getEntry2' pos store =
  case integerToFin pos (size store) of
       Nothing => Nothing
       Just idx => Just (index idx (items store))

