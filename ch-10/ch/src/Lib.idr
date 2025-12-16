module Lib

import Data.Fin
import Data.List
import Data.Nat

%default total

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

describeHelper : (input : List Int) -> (form : ListLast input) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) = "Non-empty, initial portion = " ++ show xs

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

partial
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

partial
mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (l ++ r) | SplitPair l r = merge (mergeSort l) (mergeSort r)

partial
mergeSort' : Ord a => List a -> List a
mergeSort' xs with (splitList' xs)
  mergeSort' [] | SplitNil = []
  mergeSort' [x] | SplitOne = [x]
  mergeSort' (l ++ r) | SplitPair l r = merge (mergeSort' l) (mergeSort' r)

partial
mergeSort3 : Ord a => List a -> List a
mergeSort3 xs with (splitList3 xs)
  mergeSort3 [] | SplitNil3 = []
  mergeSort3 [x] | SplitOne3 = [x]
  mergeSort3 (l ++ r) | SplitPair3 l r = merge (mergeSort3 l) (mergeSort3 r)

data MySnocList ty = EmptyMySnoc | MySnoc (MySnocList ty) ty

reverseSnoc : MySnocList ty -> List ty
reverseSnoc EmptyMySnoc = []
reverseSnoc (MySnoc xs x) = x :: reverseSnoc xs

data SnocList : List a -> Type where
  EmptySnoc : SnocList []
  Snoc : {xs : List a} -> (rec : SnocList xs) -> {x : a} -> SnocList (xs ++ [x])

listRightNeutral : (xs : List a) -> xs ++ [] = xs
listRightNeutral [] = Refl
listRightNeutral (x::xs') = cong (x::) (listRightNeutral xs')

listAppendAssociative : (xs, ys, zs : List a) -> (xs ++ (ys ++ zs)) = ((xs ++ ys) ++ zs)
listAppendAssociative [] ys zs = Refl
listAppendAssociative (x::xs') ys zs = cong (x::) (listAppendAssociative xs' ys zs)

snocListHelper : (xs : List a) ->
                  {ys : List a} -> (acc : SnocList ys) ->
                  SnocList (ys ++ xs)
snocListHelper [] acc = rewrite listRightNeutral ys in acc
snocListHelper (x::xs') acc =
  rewrite listAppendAssociative ys [x] xs' in
          snocListHelper xs' (Snoc {x = x} acc)

total
snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelper xs EmptySnoc

total
myReverseSHelper : (xs : List a) -> SnocList xs -> List a
myReverseSHelper [] EmptySnoc = []
myReverseSHelper (xs' ++ [x]) (Snoc rec) = x :: myReverseSHelper xs' rec

total
myReverseS : List a -> List a
myReverseS xs = myReverseSHelper xs (snocList xs)

partial
isSuffix : Eq a => List a -> List a -> Bool
isSuffix input1 input2 with (snocList input1, snocList input2)
  isSuffix [] [] | (EmptySnoc, EmptySnoc) = True
  isSuffix [] (ys ++ [y]) | (EmptySnoc, Snoc ysrec) = True
  isSuffix (xs ++ [x]) [] | (Snoc xsrec, EmptySnoc) = False
  isSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec, Snoc ysrec) =
      if x == y
         then isSuffix xs ys | (xsrec, ysrec)
         else False

-- Useless 'ListLast' implementation.
data ListLast2 : List a -> Type where
  EmptyLast : ListLast2 []
  NonEmptyLast : (z : a) -> ListLast2 [z]
  RecLast : {z : a} -> (rec : ListLast2 (xs ++ [z])) -> ListLast2 (x::xs ++ [z])

listLast2 : (xs : List a) -> ListLast2 xs
listLast2 [] = EmptyLast
listLast2 (y::ys) with (listLast2 ys)
  listLast2 (y::[]) | EmptyLast = NonEmptyLast y
  listLast2 (y::[z]) | NonEmptyLast z = RecLast {xs = []} (NonEmptyLast z)
  listLast2 (y::(x::xs ++ [z])) | rec@(RecLast _) = RecLast {xs = x::xs} rec

-- This is some failed attempt to implement recursive `SplitList` view.
data SplitList4 : List a -> Type where
  SplitNil4 : SplitList4 []
  SplitOne4 : SplitList4 [z]
  SplitRecEQ4 : (l : List a) -> (z : a) -> (r : List a) ->
                {auto eqLen : length r = length l} ->
                (recNE : SplitList4 (l ++ [z] ++ r)) ->
                {y : a} -> SplitList4 ((y::l) ++ (z::r))
  SplitRecNE4 : (l : List a) ->  (z : a) -> (r : List a) ->
                {auto eqLen : length r = length (l ++ [z])} ->
                (recEQ : SplitList4 ((l ++ [z])++ r)) ->
                {y : a} -> SplitList4 (y::l ++ [z] ++ r)

listLenZero : (xs : List a) -> length xs = Z -> xs = []
listLenZero [] _ = Refl
listLenZero (x::xs') Refl impossible

splitList4 : (xs : List a) -> SplitList4 xs
splitList4 [] = SplitNil4
splitList4 [x] = SplitOne4
splitList4 (x::xs') =
  case splitList4 xs' of
       SplitNil4 => SplitOne4
       one@(SplitOne4 {z = z}) =>
          let r = SplitRecEQ4 [] z [] one {y = x}
          in r
       rec@(SplitRecEQ4 l z r rec2 {y = y} {eqLen = eqLen}) =>
            case listLast (y::l) of
                 Empty impossible
                 {-
                 Empty =>
                   let rec' : SplitList4 (y :: (z :: []))
                          = rewrite sym (listLenZero r eqLen) in rec
                       t = SplitRecNE4 [] y [z] rec' {y = x}
                   --in rewrite listLenZero r eqLen in ?c0
                   in ?c0
                   -}
                 NonEmpty (y::ls) e =>
                   let
                       lenPrf : S (length r) === length ((ls ++ [e]) ++ [e])
                                = ?c1
                       t = SplitRecNE4 l e (z::r) ?b8 {eqLen = lenPrf} {y = x}
                     in ?c2
                 NonEmpty [] e => ?c3
       rec@(SplitRecNE4 l z r _ {y = y} {eqLen = eqLen}) =>
         let
             lenPrf : length r === length (y::l)
                        = rewrite eqLen in sym (snocLen z l)
             t = SplitRecEQ4 (y::l) z r rec {eqLen = lenPrf} {y = x}
         in t

data MySplitRec : List a -> Type where
  MySplitRecNil : MySplitRec []
  MySplitRecOne : MySplitRec [x]
  MySplitRecPair : (left : List a) -> (right : List a) ->
                   Lazy (MySplitRec left) -> Lazy (MySplitRec right) ->
                   MySplitRec (left ++ right)

divHalf : (n : Nat) -> Nat
divHalf Z = Z
divHalf (S Z) = Z
divHalf (S (S t)) = S (divHalf t)

divHalfLteSelf : (x : Nat) -> divHalf x `LTE` x
divHalfLteSelf Z = LTEZero
divHalfLteSelf (S Z) = LTEZero
divHalfLteSelf (S (S k)) = let rec = divHalfLteSelf k in LTESucc (lteSuccRight rec)

total
divHalfSuccLteSelf : (n : Nat) -> divHalf (S n) `LTE` n
divHalfSuccLteSelf Z = LTEZero
divHalfSuccLteSelf (S Z) = LTESucc LTEZero
divHalfSuccLteSelf (S (S k)) = let rec = divHalfSuccLteSelf k in LTESucc (lteSuccRight rec)

-- I don't use it, but anyway.
splitAtSuccSndEq' : (n : Nat) -> (x : a) -> (xs : List a) ->
                    snd (splitAt (S n) (x::xs)) = snd (splitAt n xs)
splitAtSuccSndEq' Z _ xs = Refl
splitAtSuccSndEq' (S k) _ xs with (splitAt (S k) xs)
  _ | (tk, dr) = Refl

appendSplitAtEqSelf : (n : Nat) -> (xs : List a) -> (xs === uncurry (++) (splitAt n xs))
--appendSplitAtEqSelf : (n : Nat) -> (xs : List a) -> (xs === let (ll, rr) =  splitAt n xs in ll ++ rr)
appendSplitAtEqSelf Z xs = Refl
appendSplitAtEqSelf (S k) [] = Refl
appendSplitAtEqSelf (S k) (x::xs') with (splitAt k xs') proof 0 eq
  _ | (l, r) =
        let rec = appendSplitAtEqSelf k xs' in
            rewrite rec in
            rewrite eq in Refl

total
splitAtFstLte : (n : Nat) -> (xs : List a) -> length (fst (splitAt n xs)) `LTE` n
splitAtFstLte Z xs = LTEZero
splitAtFstLte (S k) [] = LTEZero
splitAtFstLte (S k) (x::xs') with (splitAt k xs') proof 0 eq
  _ | (tk, dr) = let rec = splitAtFstLte k xs' in
                     rewrite cong fst (sym eq) in
                     LTESucc rec

total
splitConsSndLteSucc : (y : a) -> {n, m : Nat} -> {xs : List a} ->
                        length (snd (splitAt n     xs))  `LTE` m ->
                        length (snd (splitAt n (y::xs))) `LTE` S m
splitConsSndLteSucc _ {n = Z} {xs = xs} lte = LTESucc lte
splitConsSndLteSucc _ {n = (S Z)} {xs = []} _ = LTEZero
splitConsSndLteSucc _ {n = (S (S k))} {xs = []} _ = LTEZero
splitConsSndLteSucc y {n = (S k)} {xs = x::xs'} lte with (splitAt k xs') proof 0 eq
  _ | (l, r) with (splitAt k (x::xs')) proof 0 eq2
    _ | (xl, xr) =
        let rec = splitConsSndLteSucc x {n = k} {m = m} {xs = xs'} (rewrite eq in lte)
        in rewrite cong snd (sym eq2) in rec

-- I need stronger inequality and don't use this. See next one.
total
splitHalfSndLteSuccHalf : (xs : List a) ->
                    length (snd (splitAt (divHalf (length xs)) xs)) `LTE` S (divHalf (length xs))
splitHalfSndLteSuccHalf [] = LTEZero
splitHalfSndLteSuccHalf [x] = LTESucc LTEZero
splitHalfSndLteSuccHalf (_::x::xs') with (splitAt (divHalf (length xs')) (x::xs')) proof 0 eq
  _ | (l, r) =
      let recLte = splitHalfSndLteSuccHalf xs'
          r = splitConsSndLteSucc x {m = S (divHalf (length xs'))} recLte
          --r' = replace {p = \y => LTE (length (snd y)) (S (S (divHalf (length xs'))))} eq r
      --in r'
      in rewrite cong snd (sym eq) in r

total
splitHalfSndLteHalfSucc : (xs : List a) ->
                    length (snd (splitAt (divHalf (length xs)) xs)) `LTE` (divHalf (S (length xs)))
splitHalfSndLteHalfSucc [] = LTEZero
splitHalfSndLteHalfSucc [x] = LTESucc LTEZero
splitHalfSndLteHalfSucc (x1::x2::xs') with (splitAt (divHalf (length xs')) (x2::xs')) proof 0 eq
  _ | (l, r) =
      let rec = splitConsSndLteSucc x2 (splitHalfSndLteHalfSucc xs')
      in  rewrite cong snd (sym eq) in rec

-- Here is my SplitList covering function. Metric `m` is used to convince
-- Idris, that list `xs` decreases in recursive call.
mySplitList : (xs : List a) -> {m : Nat} -> {auto prf : length xs `LTE` m} -> MySplitRec xs
mySplitList [] = MySplitRecNil
mySplitList [x] = MySplitRecOne
mySplitList (x1::x2::xs') {m = S t} {prf = LTESucc lte} with (splitAt (divHalf (length xs')) (x2::xs')) proof 0 eq
  _ | (l, r) with (t)
    _ | Z impossible
    _ | S k =
        let
            fstPrf : LTE (length l) (divHalf (length xs'))
                   = rewrite cong fst (sym eq) in
                             splitAtFstLte (divHalf (length xs')) (x2::xs')
            fstRecPrf : LTE (S (length l)) (S k)
                      = LTESucc (fstPrf `transitive` divHalfLteSelf (length xs'))
                               `transitive` lte
            fstRec = mySplitList (x1::l) {m = S k} {prf = fstRecPrf}
            sndPrf : LTE (length r) (S (divHalf (S (length xs'))))
                    = rewrite cong snd (sym eq) in
                              splitConsSndLteSucc x2 (splitHalfSndLteHalfSucc xs')
            prf3 : LTE (S (divHalf (S (length xs')))) (S (length xs'))
                    = LTESucc (divHalfSuccLteSelf (length xs'))
            sndRecPrf : LTE (length r) (S k)
                      = (sndPrf `transitive` prf3) `transitive` lte
            sndRec = mySplitList r {m = S k} {prf = sndRecPrf}
            rec = MySplitRecPair (x1::l) r (Delay fstRec) (Delay sndRec)
        in  rewrite appendSplitAtEqSelf (divHalf (length xs')) (x2::xs') in
            rewrite eq in
                    rec
