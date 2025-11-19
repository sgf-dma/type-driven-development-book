
import Data.List
import Control.WellFounded
import Data.Nat

%default total

-- Works only with 'assert_smaller', though the argument is obviously smaller.
partial
f : (xs : List a) -> List a
f [] = []
--f (x::xs') = f (assert_smaller (x::xs') (drop 1 (x::xs')))
f (x::xs') = f (drop 1 (x::xs'))

-- I may use special type to fix this, but..
data DropList : Nat -> List a -> Type where
  DropE : DropList n []
  Drop0 : (xs : List a) -> DropList Z xs
  Drop1 : {x : a} -> {xs : List a} -> DropList k xs -> DropList (S k) (x::xs)

total
dropList : (n : Nat) -> (xs : List a) -> DropList n xs
dropList Z xs = Drop0 xs
dropList (S k) [] = DropE
dropList (S k) (x::xs) = Drop1 (dropList k xs)

total
f2 : (xs : List Int) -> List Int
f2 [] = []
f2 (x::xs') with (dropList 1 (x::xs'))
  f2 (x::[]) | Drop1 DropE = f2 []
  f2 (x::ys) | Drop1 (Drop0 ys) = f2 ys

-- It stil won't work for any n.
partial
f3 : (n : Nat) -> (xs : List a) -> List (List a)
f3 _ [] = [[]]
f3 Z (x::xs') = [x::xs']
f3 (S k) (x::xs') with (dropList 1 (x::xs'))
  f3 (S k) (x::[]) | Drop1 DropE =
    case f3 k [] of
         ([]::_) => [[]]
         (t::_) => t :: f3 (S k) t
         _ => ?f3undef1
  f3 (S k) (x::ys) | Drop1 (Drop0 ys) =
    case f3 k ys of
         ([]::_) => [[]]
         (t::_) => t :: f3 (S k) t
         _ => ?f3undef2

-- I may try more complicated type, but..
data DropNList : Nat -> List a -> Type where
  DropNE : DropNList n []
  DropN0 : (xs : List a) -> DropNList Z xs
  DropN : {y : a} -> {ys, xs : List a} -> {n, k : Nat} ->
          DropNList k xs ->
          {auto prf : n = plus (length (y::ys)) k} ->
          DropNList n ((y::ys) ++ xs)

total
dropNList : (n : Nat) -> (xs : List a) -> DropNList n xs
dropNList Z xs = DropN0 xs
dropNList (S t) [] = DropNE
dropNList (S t) (x::xs') =
  case dropNList t xs' of
       DropNE => DropN {ys = []} DropNE
       DropN0 _ => DropN {ys = []} (DropN0 xs')
       DropN {y = y} {ys = ys} {prf = prf} dl =>
            DropN {y = x} {ys = y::ys} {prf = cong S prf} dl

-- It won't help.
partial
f4 : (n : Nat) -> (xs : List a) -> List (List a)
f4 Z xs = [xs]
f4 (S t) xs with (dropNList (S t) xs)
  f4 (S t) [] | DropNE = [[]]
  f4 (S t) xs | DropN0 xs impossible
  f4 (S t) (y::(ys ++ [])) | DropN {y = y} {ys = ys} _ = [y::ys]
  f4 (S t) (y::(ys ++ xs')) | DropN {y = y} {ys = ys} _ =
    -- Note, that correct recursive call does not pass totality check, but..
    (y::ys) :: f4 (S t) xs'
    -- incorrect one will pass it successfully and function will be total.
    --(y::ys) :: f4 (S t) (ys++xs')

-- So, the real fix is to add an extra argument, which will structurally show
-- the decreasing argument.
total
g : (xs : List a) -> {l : Nat} -> {auto prf : l = length xs} -> List a
g [] {l = Z} = []
g (x::xs') {l = S (length xs')} {prf = Refl} =
  let t = g (drop 1 (x::xs')) {l = length xs'}
  in  t

dropLengthLTE : (k : Nat) -> (xs : List a) ->
        (length (drop k xs)) `LTE` (length xs)
dropLengthLTE Z [] = LTEZero
dropLengthLTE (S t) [] = LTEZero
dropLengthLTE Z (x::xs') = let r = dropLengthLTE Z xs' in LTESucc r
dropLengthLTE (S t) (x::xs') =
  let r = dropLengthLTE t xs'
  in  lteSuccRight r

-- It's more complex for n, but still works.
total
g4 : (xs : List a) -> {l : Nat} -> {auto prf : length xs `LTE` l} -> List a
g4 [] = []
g4 (x::xs') {l = Z} impossible
g4 (x::xs') {l = S t} {prf = LTESucc lte} =
  --let t = g4 (drop 3 (x::xs')) {prf = trans (dropLengthLTE 2 xs') lte}
  let t = g4 (drop 3 (x::xs')) {prf = transitive (dropLengthLTE 2 xs') lte}
  in  t

