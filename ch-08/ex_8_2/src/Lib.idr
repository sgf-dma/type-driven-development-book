module Lib

import Data.Nat
import Data.Vect

-- Ex 8.2.1
myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m =
  rewrite plusZeroRightNeutral m
  -- rw[plusZeroRightNeutral]
  -- rfl
  in Refl
myPlusCommutes (S k) m =
  rewrite myPlusCommutes k m
  in plusSuccRightSucc m k  -- exact plusSuccRightSucc
          {-
  in rewrite plusSuccRightSucc m k
          -- rw [plusSuccRightSucc]
          -- rfl
          in Refl
          -}

-- Ex 8.2.2
export
myReverse : {n : Nat} -> Vect n a -> Vect n a
myReverse xs = reverse' [] xs
  where
    reverse' : {n : Nat} -> {m : Nat} -> Vect n a -> Vect m a -> Vect (n + m) a
    reverse' {n = n} acc Nil = rewrite plusZeroRightNeutral n in acc
    reverse' {n = n} {m = S t} acc (x :: xs) =
      rewrite sym (plusSuccRightSucc n t) in reverse' (x::acc) xs
