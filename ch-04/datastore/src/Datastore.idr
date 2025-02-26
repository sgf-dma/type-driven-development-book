module Datastore

import Data.Vect

public export
data DataStore : Type where
  MkData : (size : Nat) -> Vect size String -> DataStore

export
size : DataStore -> Nat
size (MkData n _) = n

export
items : (store : DataStore) -> Vect (size store) String
items (MkData _ xs) = xs

export
addToStore : DataStore -> String -> DataStore
--addToStore (MkData n xs) y = MkData (S n) (xs `snoc` y)
{-
addToStore (MkData _ []) y = MkData _ [y]
addToStore (MkData _ (x :: xs)) y =
  let MkData n zs = addToStore (MkData _ xs) y
  in  MkData (S n) (x :: zs)
-}
addToStore (MkData _ xs) y = MkData _ (snocVect xs)
  where
    snocVect : Vect n String -> Vect (S n) String
    snocVect [] = [y]
    snocVect (x :: xs) = x :: snocVect xs

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

