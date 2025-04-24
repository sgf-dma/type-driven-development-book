module Utils

import Data.Fin
import Data.Vect

-- Conversion of Nat to Fin without Maybe. Version with pattern matching.
export
total natToFin2 : (m : Nat) -> (n : Nat) -> Fin (maximum (S m) n)
natToFin2 Z Z = FZ {k = Z}
natToFin2 Z (S k) = FZ {k = k}
natToFin2 (S k) Z = FS (natToFin2 k Z)
natToFin2 (S k) (S t) = FS (natToFin2 k t)

-- Convert Nat to minimal possible Fin.
export
total natToFinMin : (k : Nat) -> Fin (S k)
natToFinMin Z     = FZ {k = Z}
natToFinMin (S t) = FS (natToFinMin t)

total max' : Nat -> Nat -> Nat
max' m n = case compare m n of
                LT => n
                EQ => m
                GT => m

-- Version of natToFin2 based on compare without explicit pattern matching.
export
total natToFin3 : (m : Nat) -> (n : Nat) -> Fin (max' (S m) n)
natToFin3 m Z = natToFinMin m
natToFin3 m n@(S t) with (compare (S m) n)
  _ | LT = natToFinMin t
  _ | EQ = natToFinMin m
  _ | GT = natToFinMin m

-- Add empty list elements to vector if needed, so the vector will contain
-- element with index m.
export
padEmpty : (m : Nat) -> {t : Nat} -> Vect t (List a) -> Vect (maximum (S m) t) (List a)
padEmpty Z     {t = Z}   vs = [[]]
padEmpty Z     {t = S _} vs = vs
padEmpty (S k) {t = Z}   _  = go (S (S k))
  where
    go : (n : Nat) -> Vect n (List a)
    go Z = []
    go (S k) = [] :: go k
padEmpty (S k) {t = S t} (v :: vs) = v :: padEmpty k vs
