module Lib

import Data.Fin
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

snocLeftEqConsRight : (ys : List a) -> (z : a) -> (r : List a) -> (ys++[z]) ++ r = ys ++ (z::r)
snocLeftEqConsRight [] z r = Refl
snocLeftEqConsRight (y::ys') z r =
  rewrite (snocLeftEqConsRight ys' z r) in Refl

total
splitList : (input : List a) -> SplitList input
splitList input = splitListHelp input input
where
  splitListHelp : List a -> (input : List a) -> SplitList input
  splitListHelp _ [] = SplitNil
  splitListHelp _ [x] = SplitOne
  splitListHelp (_ :: _ :: counter) (item :: items)
      = case splitListHelp counter items of
             SplitNil => SplitOne
             SplitOne {x} => SplitPair [item] [x]
             SplitPair lefts rights => SplitPair (item :: lefts) rights
  splitListHelp _ items = SplitPair [] items

total
splitList' : (xs : List a) -> SplitList xs
splitList' [] = SplitNil
splitList' [x] = SplitOne
splitList' (x::xs') =
  case splitList' xs' of
       SplitNil => SplitOne
       SplitOne {x = y} => SplitPair [x] [y]
       SplitPair l r => case compare (length l) (length r) of
            LT => SplitPair (x::l) r
            EQ => SplitPair (x::l) r
            GT => case listLast l of
                 Empty => SplitPair [x] r
                 NonEmpty ys y =>
                       let t = SplitPair (x::ys) (y::r)
                       in rewrite (snocLeftEqConsRight ys y r) in t

data SplitList2 : List a -> Type where
  SplitNil2 : SplitList2 []
  SplitOne2 : SplitList2 [x]
  SplitEq2 : (l : List a) -> (r : List a) -> {auto eqPrf : length l = length r} -> SplitList2 (l ++ r)
  SplitNeq2 : (l : List a) -> (r : List a) -> {auto neqPrf : length l = S (length r)} -> SplitList2 (l ++ r)

snocLen : (x : a) -> (ys : List a) -> S (length ys) = length (ys ++ [x])
snocLen x [] = Refl
snocLen x (y::ys') = rewrite (snocLen x ys') in Refl

total
splitList2 : (xs : List a) -> SplitList2 xs
splitList2 [] = SplitNil2
splitList2 [x] = SplitOne2
splitList2 (x::xs') =
  case splitList2 xs' of
       SplitNil2 => SplitOne2
       SplitOne2 {x = y} => SplitEq2 [x] [y]
       SplitEq2 l r {eqPrf = eqPrf} =>
            let neqPrf = cong S eqPrf
            in  SplitNeq2 (x::l) r
       SplitNeq2 l r {neqPrf = neqPrf} => case listLast l of
            Empty impossible
            NonEmpty ys y =>
                 let eqPrf = rewrite snocLen y ys in neqPrf
                  in rewrite (snocLeftEqConsRight ys y r)
                  in SplitEq2 (x::ys) (y::r) {eqPrf = eqPrf}

data SplitList3 : List a -> Type where
  SplitNil3 : SplitList3 []
  SplitOne3 : SplitList3 [x]
  SplitPair3 : (l : List a) -> (r : List a) ->
               {auto lenDiff : Fin 2} ->
               {auto lenPrf : length l = finToNat lenDiff + length r} ->
               SplitList3 (l ++ r)

total
splitList3 : (xs : List a) -> SplitList3 xs
splitList3 [] = SplitNil3
splitList3 [x] = SplitOne3
splitList3 (x::xs') =
  case splitList3 xs' of
       SplitNil3 => SplitOne3
       SplitOne3 {x = y} => SplitPair3 [x] [y] {lenDiff = FZ}
       SplitPair3 l r {lenDiff = FZ} {lenPrf = lenPrf} =>
            let t = SplitPair3 (x::l) r {lenDiff = FS FZ} {lenPrf = cong S lenPrf}
            in  t
       SplitPair3 l r {lenDiff = FS FZ} {lenPrf = lenPrf} => case listLast l of
            Empty impossible
            NonEmpty ys y =>
                let lenPrf' = rewrite snocLen y ys in lenPrf
                in rewrite (snocLeftEqConsRight ys y r)
                in SplitPair3 (x::ys) (y::r) {lenPrf = lenPrf'}
       SplitPair3 l r {lenDiff = FS (FS k)} impossible

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (l ++ r) | SplitPair l r = merge (mergeSort l) (mergeSort r)

mergeSort' : Ord a => List a -> List a
mergeSort' xs with (splitList' xs)
  mergeSort' [] | SplitNil = []
  mergeSort' [x] | SplitOne = [x]
  mergeSort' (l ++ r) | SplitPair l r = merge (mergeSort' l) (mergeSort' r)

mergeSort3 : Ord a => List a -> List a
mergeSort3 xs with (splitList3 xs)
  mergeSort3 [] | SplitNil3 = []
  mergeSort3 [x] | SplitOne3 = [x]
  mergeSort3 (l ++ r) | SplitPair3 l r = merge (mergeSort3 l) (mergeSort3 r)
