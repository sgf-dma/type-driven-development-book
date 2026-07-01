module Lib

import Data.Bits
import Data.Nat.Views


%default total

-- Ex. 1.
export
every_other : Stream a -> Stream a
every_other (x::y::xs) = y :: every_other xs

-- Ex. 2.
export
data InfList : Type -> Type where
  (::) : (val : a) -> Inf (InfList a) -> InfList a

total
export
countFrom : Integer -> InfList Integer
countFrom n = n :: countFrom (n + 1)

total
export
getPrefix : (count : Nat) -> InfList a -> List a
getPrefix Z _ = []
getPrefix (S k) (v::infvs) = v :: getPrefix k infvs

export
Functor InfList where
  map f (v::infvs) = f v :: map f infvs

-- Ex. 3.
randoms : Integer -> Stream Integer
randoms seed =
  let seed' = 1664525 * seed + 1013904223 in (seed' `shiftR` 2) :: randoms seed'

randomNats : Stream Integer -> Stream Nat
randomNats (r::rs) = integerToNat (if r < 0 then abs r else r) :: randomNats rs

public export
data Face = Heads | Tails

export
Eq Face where
  Heads == Heads = True
  Tails == Tails = True
  _ == _ = False

export
coinFlips : (count : Nat) -> Stream Nat -> List Face
coinFlips 0 _ = []
coinFlips (S k) (r::rs) =
  case half r of
       HalfOdd _  => Tails :: coinFlips k rs
       HalfEven _ => Heads :: coinFlips k rs

-- Ex. 4.
export
square_root_approx : (num : Double) -> (approx : Double) -> Stream Double
square_root_approx num approx = approx :: square_root_approx num ((approx + num/approx)/2)

-- Ex. 5.
square_root_bound : (max : Nat) -> (num : Double) -> (bound : Double) ->
                    (approxs : Stream Double) -> Double
square_root_bound Z _ _ (ap::_) = ap
square_root_bound (S m) num bound (ap::aps) =
  if abs (ap*ap - num) < bound
     then ap
     else square_root_bound m num bound aps

total
square_root : (num : Double) -> Double
square_root num = square_root_bound 100 num 0.00000000001 (square_root_approx num num)

