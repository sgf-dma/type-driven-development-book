
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
  DropE : DropList (S n) []
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
  f2 (x::[]) | Drop1 DropE impossible
  f2 (x::ys) | Drop1 (Drop0 ys) = f2 ys

-- It stil won't work for any n.
partial
f3 : (n : Nat) -> (xs : List a) -> List (List a)
f3 _ [] = []
f3 Z (x::xs') = [x::xs']
f3 (S k) (x::xs') with (dropList 1 (x::xs'))
  f3 (S k) (x::[]) | Drop1 DropE impossible
  f3 (S k) (x::ys) | Drop1 (Drop0 ys) =
    case f3 k ys of
         [] => []
         (t::_) => t :: f3 (S k) t

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

dropLengthLTE : (k : Nat) -> (xs : List a) -> (length (drop k xs)) `LTE` (length xs)
dropLengthLTE Z [] = LTEZero
dropLengthLTE (S t) [] = LTEZero
dropLengthLTE Z (x::xs')     = let r = dropLengthLTE Z xs' in LTESucc r
dropLengthLTE (S t) (x::xs') = let r = dropLengthLTE t xs' in lteSuccRight r

-- It's more complex for values greater, than 1
total
g3' : (xs : List a) -> {l : Nat} -> {auto prf : length xs `LTE` l} -> List a
g3' [] = []
g3' (x::xs') {l = Z} impossible
g3' (x::xs') {l = S k} {prf = LTESucc lte} =
  --let t = g3' (drop 3 (x::xs')) {prf = trans (dropLengthLTE 2 xs') lte}
  let t = g3' (drop 3 (x::xs')) {prf = transitive (dropLengthLTE 2 xs') lte}
  in  t

-- Or i may match on LTE directly.
total
g3'2 : (xs : List a) -> {l : Nat} -> {auto prf : length xs `LTE` l} -> List a
g3'2 [] = []
g3'2 (x::xs') {prf = LTEZero} impossible
g3'2 (x::xs') {prf = LTESucc lte} =
  let t = g3'2 (drop 3 (x::xs')) {prf = transitive (dropLengthLTE 2 xs') lte}
  in  t

-- Or with arbitrary n
total
g3'3 : (n : Nat) -> (xs : List a) -> {l : Nat} -> {auto prf : length xs `LTE` l} -> List a
g3'3 n [] = []
g3'3 n (x::xs') {prf = LTEZero} impossible
g3'3 Z (x::xs') {prf = LTESucc lte} = (x::xs')
g3'3 (S k) (x::xs') {prf = LTESucc lte} =
  let t = g3'3 (S k) (drop (S k) (x::xs')) {prf = transitive (dropLengthLTE k xs') lte}
  in  t

-- And, finally, here is total implementation of f3.
total
g3 : (n : Nat) -> (xs : List a) -> {l : Nat} -> {auto prf : length xs `LTE` l} -> List (List a)
g3 n [] = [[]]
g3 n (x::xs') {prf = LTEZero} impossible
g3 Z (x::xs') {prf = LTESucc lte} = [x::xs']
g3 (S k) (x::xs') {prf = LTESucc lte} =
  let ys : ?
      ys = drop (S k) (x::xs')
  in case ys of
         [] => []
         _  => ys :: g3 (S k) ys {prf = transitive (dropLengthLTE k xs') lte}

-- Total implementation of f4 is slightly more difficult..

lteSelf : {n : Nat} -> LTE n n
lteSelf {n = Z} = LTEZero
lteSelf {n = S k} = LTESucc lteSelf

-- I can't prove this for existing 'splitAt' definition, because 'let' clause
-- in 'splitAt' definition doesn't reduce.
splitAtSndLength' : (n : Nat) -> {x : a} -> (xs : List a) ->
                    length (snd (splitAt (S n) (x::xs))) `LTE` length xs
splitAtSndLength' Z [] = LTEZero
splitAtSndLength' Z (x::xs') = LTESucc lteSelf
splitAtSndLength' (S k) [] = LTEZero
splitAtSndLength' (S k) (y::xs') =
  let r = lteSuccRight (splitAtSndLength' k {x = y} {xs = xs'})
  in  ?failed1

-- But if i define 'splitAt' without pattern match in 'let', ..
mySplitAt : Nat -> List a -> (List a, List a)
mySplitAt 0 xs = ([], xs)
mySplitAt (S k) [] = ([], [])
mySplitAt (S k) (x :: xs) = let z = mySplitAt k xs in (x :: fst z, snd z)

-- (this is not used, but anyway)
splitAtSuccSndEq : (n : Nat) -> (x : a) -> (xs : List a) ->
                   snd (mySplitAt (S n) (x::xs)) = snd (mySplitAt n xs)
splitAtSuccSndEq Z _ _ = Refl
splitAtSuccSndEq (S k) _ _ = Refl

-- ..i can finally prove 'splitAtSndLength'.
splitAtSndLength : (n : Nat) -> {x : a} -> (xs : List a) ->
                   length (snd (mySplitAt (S n) (x::xs))) `LTE` length xs
splitAtSndLength Z [] = LTEZero
splitAtSndLength Z (_::_) = LTESucc lteSelf
splitAtSndLength (S _) [] = LTEZero
splitAtSndLength (S k) (y::xs') =
  let r = lteSuccRight (splitAtSndLength k {x = y} {xs = xs'})
  -- Note the result type:
  --        a4 : LTE (length (snd (mySplitAt k xs'))) (S (length xs'))
  -- this is exactly the type of `splitAtSndLength2`, when (xs = x::xs'). So,
  -- these two functions are indeed the same.
  --in  rewrite splitAtSuccSndEq k y xs' in ?a4 -- r
  in r

-- But with my `splitAt` definition much simpler proof will suffice!
splitAtSndLength2 : (n : Nat) -> (xs : List a) ->
                    length (snd (mySplitAt n xs)) `LTE` length xs
splitAtSndLength2 Z [] = LTEZero
splitAtSndLength2 Z (x::xs') = LTESucc lteSelf
splitAtSndLength2 (S k) [] = LTEZero
splitAtSndLength2 (S k) (x::xs') = let r = splitAtSndLength2 k xs' in lteSuccRight r

total
g4 : (n : Nat) -> (xs : List a) -> {l : Nat} -> {auto prf : length xs `LTE` l} -> List (List a)
g4 Z xs = [xs]
g4 (S t) [] = [[]]
g4 (S t) {l = S n} (x::xs') {prf = LTESucc lte} =
  let z : ?
      z = mySplitAt (S t) (x::xs')
      -- I can use this proof..
      prf = transitive (splitAtSndLength t {x = x} {xs = xs'}) lte
      r = g4 (S t) {l = n} {prf = prf} (snd z)
      -- but with my `splitAt` definition much simpler proof will also be enough
      prf2 = transitive (splitAtSndLength2 t {xs = xs'}) lte
      r2 = g4 (S t) {l = n} {prf = prf2} (snd z)
  in  case r2 of
           [[]] => [fst z]
           rs => fst z :: rs
