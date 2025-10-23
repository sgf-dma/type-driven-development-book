module Lib

import Data.List

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

describeHelper : (input : List Int) -> (form : ListLast input) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) = "Non-empty, initial portino = " ++ show xs

total
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x::xs) =
  case listLast xs of
       Empty => NonEmpty [] x
       r@(NonEmpty ys y) => NonEmpty (x::ys) y

describeListEnd : List Int -> String
describeListEnd xs = describeHelper xs (listLast xs)

describeListEnd2 : List Int -> String
describeListEnd2 input with (listLast input)
  describeListEnd2 [] | Empty = "Empty"
  describeListEnd2 (xs ++ [x]) | (NonEmpty xs x) = "Non-empty, initial portion = " ++ show xs

myReverse : List a -> List a
myReverse input with (listLast input)
  myReverse [] | Empty = []
  myReverse (xs ++ [x]) | (NonEmpty xs x) = x :: myReverse xs

data SplitList : List a -> Type where
  SplitNil : SplitList []
  SplitOne : SplitList [x]
  SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)

snocLeftEqConsRight : (xs : List a) -> (x : a) -> (r : List a) ->
                      (xs++[x]) ++ r = xs ++ (x::r)
snocLeftEqConsRight [] x r = Refl
snocLeftEqConsRight (z::zs) x r =
  rewrite (snocLeftEqConsRight zs x r) in Refl

splitList' : (xs : List a) -> SplitList xs
splitList' [] = SplitNil
splitList' [x] = SplitOne
splitList' (y::ys) =
  case splitList' ys of
       SplitNil => SplitOne
       SplitOne {x = x} => SplitPair [y] [x]
       SplitPair l r => case compare (length l) (length r) of
            LT => SplitPair (y::l) r
            EQ => SplitPair (y::l) r
            GT => case listLast l of
                 Empty => SplitPair [y] r
                 NonEmpty xs x =>
                       let t = SplitPair (y::xs) (x::r)
                       in rewrite (snocLeftEqConsRight xs x r) in t

data SplitList2 : List a -> Type where
  SplitNil2 : SplitList2 []
  SplitOne2 : SplitList2 [x]
  SplitEq : (l : List a) -> (r : List a) -> {auto eqPrf : length l = length r} -> SplitList2 (l ++ r)
  SplitNeq : (l : List a) -> (r : List a) -> {auto neqPrf : length l = S (length r)} -> SplitList2 (l ++ r)

snocLen : (x : a) -> (xs : List a) -> S (length xs) = length (xs ++ [x])

splitList2 : (xs : List a) -> SplitList2 xs
splitList2 [] = SplitNil2
splitList2 [x] = SplitOne2
splitList2 (y::ys) =
  case splitList2 ys of
       SplitNil2 => SplitOne2
       SplitOne2 {x = x} => SplitEq [y] [x]
       SplitEq l' r' {eqPrf = eqPrf} =>
            let neqPrf = cong S eqPrf
            in  SplitNeq (y::l') r'
       SplitNeq l r {neqPrf = neqPrf} => case listLast l of
            Empty impossible
            NonEmpty xs x =>
                 let eqPrf = rewrite snocLen x xs in neqPrf
                  in rewrite (snocLeftEqConsRight xs x r)
                  in SplitEq (y::xs) (x::r) {eqPrf = eqPrf}

partial
mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList' xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (l ++ r) | SplitPair l r = merge (mergeSort l) (mergeSort r)
