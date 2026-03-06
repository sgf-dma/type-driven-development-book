
import Data.List
import Data.Nat

divHalf : (n : Nat) -> Nat
divHalf Z = Z
divHalf (S Z) = Z
divHalf (S (S t)) = S (divHalf t)

--total
--f1 : (xs : List Int) -> {m : Nat} -> {auto prf : length xs `LTE` m} -> Int
--f1 [] = 0
--f1 [x] = x
--f1 (_::x2::xs') {m = S Z} {prf = LTESucc lte} = absurd lte
--f1 (x1::x2::xs') {m = S t@(S k)} {prf = LTESucc (LTESucc lte)} with (splitAt (divHalf (length xs')) (x2::xs')) proof 0 eq
--  _ | (l, r) =
--      let rec = f1 (x1::l) {m = S k} {prf = ?b3}
--          --rec = f1 (x1::l) {m = t} {prf = ?b3}
--      in rec

total
f2 : (xs : List Int) -> {m : Nat} -> {auto prf : length xs `LTE` m} -> Int
f2 [] = 0
f2 [x] = x
f2 (x1::x2::xs') {m = S t} {prf = LTESucc lte} with (splitAt (divHalf (length xs')) (x2::xs')) proof 0 eq
  f2 (x1::x2::xs') {prf = LTESucc lte} | (l, r) with (t)
    f2 (x1::x2::xs') {prf = LTESucc lte} | (l, r) | Z = absurd lte
    f2 (x1::x2::xs') {prf = LTESucc (LTESucc lte)} | (l, r) | S k =
          let rec = f2 (x1::l) {m = S k} {prf = ?b1}
          in rec

--total
--f3 : (xs : List Int) -> {m : Nat} -> {auto prf : length xs `LTE` m} -> Int
--f3 [] = 0
--f3 [x] = x
--f3 (x1::x2::xs') {m = S t} {prf = LTESucc lte} with (t)
--  f3 (x1::x2::xs') {prf = LTESucc lte} | Z = absurd lte
--  f3 (x1::x2::xs') {prf = LTESucc (LTESucc lte)} | S k with (splitAt (divHalf (length xs')) (x2::xs')) proof 0 eq
--      _ | (l, r) =
--          let rec = f3 (x1::l) {m = S k} {prf = ?b2}
--          in rec

