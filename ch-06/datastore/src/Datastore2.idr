module Datastore2

import Data.List
import Data.Vect

import Schema


export
data DataStore2 : Schema -> Type where
  MkData2 : (size : Nat) -> (items : Vect size (SchemaType scm)) -> DataStore2 scm

export
size : DataStore2 scm -> Nat
size (MkData2 n _) = n

export
items : (store : DataStore2 scm) -> Vect (size store) (SchemaType scm)
items (MkData2 _ xs) = xs

schema2 : {1 scm : Schema} -> DataStore2 scm -> Schema
schema2 _ = scm

export
setSchema2 : DataStore2 scm -> (scm2 : Schema) -> Maybe (DataStore2 scm2)
setSchema2 store scm = case size store of
                       Z => Just (MkData2 _ [])
                       S _ => Nothing

export
getEntry2 : Integer -> {scm : Schema} -> DataStore2 scm -> Maybe (SchemaType scm)
getEntry2 pos store =
  case integerToFin pos (size store) of
       Nothing => Nothing
       Just idx => Just (index idx (items store))

export
getAllEntries : DataStore2 scm -> List (Nat, SchemaType scm)
getAllEntries (MkData2 size items) = zip [0..size] (toList items)

export
empty2 : DataStore2 schema
empty2 = MkData2 0 []

-- 10.3.3
export
addToStore2 : {0 scm : Schema} -> (value : SchemaType scm) ->
                                  (store : DataStore2 scm) -> DataStore2 scm
addToStore2 value (MkData2 _ items) = MkData2 _ (value::items)

public export
data Store2View : DataStore2 scm -> Type where
  SNil : Store2View Datastore2.empty2
  SAdd : {value : SchemaType scm} -> {store : DataStore2 scm} ->
         (rec : Store2View store) -> Store2View (addToStore2 value store)

export
store2View : (store : DataStore2 scm) -> Store2View store
store2View (MkData2 0 []) = SNil
store2View (MkData2 (S k) (value::items')) = SAdd (store2View (MkData2 k items'))

export
appendToStore2 : {0 scm : Schema} -> (value : SchemaType scm) ->
                                   (store : DataStore2 scm) -> DataStore2 scm
appendToStore2 value (MkData2 _ items) = MkData2 _ (items `snoc` value)

data SnocVect : Vect n a -> Type where
  Empty : SnocVect []
  Snoc : (rest : Vect m a) -> (value : a) -> SnocVect (rest `snoc` value)

snocVect : (xs : Vect n a) -> SnocVect xs
snocVect [] = Empty
snocVect (x :: xs) =
  case snocVect xs of
       Empty => Snoc [] x
       Snoc rest value => Snoc (x::rest) value

-- View store from the end.
data Store2ViewAppend : DataStore2 scm -> Type where
  SAppendNil : Store2ViewAppend Datastore2.empty2
  SAppend : {value : SchemaType scm} -> {store : DataStore2 scm} ->
          (rec : Store2ViewAppend store) -> Store2ViewAppend (appendToStore2 value store)

store2ViewAppend : (store : DataStore2 scm) -> Store2ViewAppend store
store2ViewAppend (MkData2 0 []) = SAppendNil
store2ViewAppend (MkData2 (S k) xs) with (snocVect xs)
  store2ViewAppend (MkData2 (S k) []) | Empty impossible
  store2ViewAppend (MkData2 (S k) (rest `snoc` value)) | Snoc rest value =
    SAppend (store2ViewAppend (MkData2 k rest))

export
listItems : DataStore2 schema -> List (SchemaType schema)
listItems store with (store2View store)
  listItems Datastore2.empty2 | SNil = []
  listItems (addToStore2 value store') | SAdd rec = value::(listItems store' | rec)

-- Version using Store2ViewAppend view.
export
listItems' : DataStore2 schema -> List (SchemaType schema)
listItems' store = go store <>> []
  where
    go : DataStore2 schema -> SnocList (SchemaType schema)
    go store with (store2ViewAppend store)
      go Datastore2.empty2 | SAppendNil = Lin
      go (appendToStore2 value store') | SAppend rec = (go store' | rec) :< value

-- See 10.3.3 .
testStore : DataStore2 (SString .+. (SString .+. SInt))
testStore = addToStore2 ("Mercury", "Mariner 10", 1974) $
            addToStore2 ("Venus", "Venera", 1961) $
            addToStore2 ("Uranus", "Voyager 2", 1986) $
            addToStore2 ("Pluto", "New Horizons", 2015) $
            empty2

filterKeys : (test : SchemaType scmVal -> Bool) ->
             (store : DataStore2 (scmKey .+. scmVal)) -> List (SchemaType scmKey)
filterKeys test store with (store2View store)
  filterKeys test Datastore2.empty2 | SNil = []
  filterKeys test (addToStore2 (key, val) store') | SAdd rec =
    if test val
       then key::(filterKeys test store' | rec)
       else filterKeys test store' | rec

-- Version with Store2ViewAppend . Except view constructor names, nothing
-- changed.
filterKeys' : (test : SchemaType scmVal -> Bool) ->
              (store : DataStore2 (scmKey .+. scmVal)) -> List (SchemaType scmKey)
filterKeys' test store with (store2ViewAppend store)
  filterKeys' test Datastore2.empty2 | SAppendNil = []
  filterKeys' test (appendToStore2 (key, val) store') | SAppend rec =
    if test val
       then key::(filterKeys' test store' | rec)
       else filterKeys' test store' | rec

-- Generic versions of filterKeys above.
-- Note, that though i may try to require, that sub schema is subtree of full
-- schema using implicit argument of type 'SchemaSubtree full sub', there is
-- no sense in such requirment, because no function called from this one use
-- this proof. E.g. findSubtreeValues does not need it, because it'll run for
-- any pair of schemas and build a list of subtrees, if any.
filterStore2 : {full, sub : Schema} -> (store : DataStore2 full) ->
               (test : SchemaType sub -> Bool) ->
               DataStore2 full
filterStore2 store test with (store2View store)
  filterStore2 Datastore2.empty2 _ | SNil = empty2
  filterStore2 (addToStore2 value store') test | SAdd rec =
    let match = (find test (findSubtreeValues full sub value))
    in  maybe id (\_ => addToStore2 value) match
          $ (filterStore2 store' test | rec)

-- The same with Store2ViewAppend. Nothing changed, except view constructor
-- names.
filterStore2' : {full, sub : Schema} -> (store : DataStore2 full) ->
               (test : SchemaType sub -> Bool) ->
               DataStore2 full
filterStore2' store test with (store2ViewAppend store)
  filterStore2' Datastore2.empty2 _ | SAppendNil = empty2
  filterStore2' (appendToStore2 value store') test | SAppend rec =
    let match = (find test (findSubtreeValues full sub value))
    in  maybe id (\_ => appendToStore2 value) match
          $ (filterStore2' store' test | rec)

export
searchWith : {full : Schema} -> (store : DataStore2 full) ->
             (eqFuncs : List (scm' : Schema ** SchemaType scm' -> SchemaType scm' -> Bool)) ->
             (sub : Schema) -> (subval : SchemaType sub) ->
             List (Nat, SchemaType full)
searchWith = go 0
  where
    go : (acc : Nat) ->
         {full : Schema} -> (store : DataStore2 full) ->
         (eqFuncs : List (scm' : Schema ** SchemaType scm' -> SchemaType scm' -> Bool)) ->
         (sub : Schema) -> (subval : SchemaType sub) ->
         List (Nat, SchemaType full)
    go acc {full = full} store eqFuncs sub subval with (store2View store)
      go _   {full = full} Datastore2.empty2       _       _   _      | SNil = []
      go acc {full = full} (addToStore2 el store') eqFuncs sub subval | SAdd rec =
        let eq = buildMatcher sub subval eqFuncs
            found = find eq (findSubtreeValues full sub el)
            rc = (go (acc + 1) store' eqFuncs sub subval | rec)
        in maybe id (\_ => ((acc, el)::)) found $ rc
