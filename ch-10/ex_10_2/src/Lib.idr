module Lib

import Data.Vect
import Data.Vect.Views
import Data.Nat
import Data.Nat.Views
import Data.Fin
import Data.List
import Data.List.Views
import Data.List.Views.Extra
import Data.List.Equalities


-- Ex 10.2.1
equalSuffix' : Eq a => List a -> List a -> Prelude.SnocList a
equalSuffix' xs ys with (snocList xs, snocList ys)
  equalSuffix' (xs' ++ [x]) (ys' ++ [y]) | (Snoc x xs' xrec, Snoc y ys' yrec) =
    if x /= y
       then Lin
       else (equalSuffix' xs' ys' | (xrec, yrec)) :< x
  equalSuffix' [] _ | (Empty, _) = Lin
  equalSuffix' _  [] | (_, Empty) = Lin

export
equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys = equalSuffix' xs ys <>> []

-- Ex 10.2.2
public export
data HalfNat : Nat -> Type where
  EvenHalf : (k : Nat) -> HalfNat (k + k)
  OddHalf  : (k : Nat) -> HalfNat (k + S k)

export
Eq (HalfNat n) where
  _ == _ = True

export
halfNat : (n : Nat) -> HalfNat n
halfNat Z = EvenHalf Z
halfNat (S Z) = OddHalf Z
halfNat (S (S t)) = case halfNat t of
                          EvenHalf k => let r = EvenHalf (S k) in
                                             rewrite plusSuccRightSucc k k in
                                                     r
                          OddHalf k => let r = OddHalf (S k) in
                                            rewrite plusSuccRightSucc k (S k) in
                                                    r

public export
data VectSplitHalf : Vect n a -> Type where
  VSplitEven : {k : Nat} -> (left : Vect k a) -> (right : Vect k a) -> VectSplitHalf (left ++ right)
  VSplitOdd :  {k : Nat} -> (left : Vect k a) -> (right : Vect (S k) a) -> VectSplitHalf (left ++ right)

export
Eq (VectSplitHalf xs) where
  _ == _ = True

splitAppendEqSelf : {k : Nat} -> (xs : Vect (k + m) a) -> xs === uncurry (++) (splitAt k {m} xs)
splitAppendEqSelf {k = Z} xs = Refl
splitAppendEqSelf {k = S t} [] impossible
splitAppendEqSelf {k = S t} (x::xs) with (splitAt t {m} xs) proof 0 eq
  _ | (l, r) = let rec = splitAppendEqSelf {k = t} {m} xs in
                   rewrite rec in
                   rewrite eq in
                           Refl

-- There is no sense in using 'HalfRec' (see 'MyHalfRec' definition below)
-- here, because this function does not recurse.
export
vectSplitHalf : {n : Nat} -> (xs : Vect n a) -> VectSplitHalf xs
vectSplitHalf xs {n = n} with (halfNat n)
  vectSplitHalf xs {n = k + k} | EvenHalf k with (splitAt k xs) proof 0 splitPrf
    _ | (left, right) =
        let prf = splitAppendEqSelf {k = k} {m = k} xs
         in rewrite prf in rewrite splitPrf in VSplitEven left right
  vectSplitHalf xs {n = k + S k} | OddHalf k with (splitAt k xs) proof 0 splitPrf
    _ | (left, right) =
        let prf = splitAppendEqSelf {k = k} {m = S k} xs
         in rewrite prf in rewrite splitPrf in VSplitOdd left right

-- Or i may define 'HalfNat' slightly different, providing proof as part of
-- constructor.
data HalfNat' : Nat -> Type where
  EvenHalf' : (k : Nat) -> (halvesEq : n = k + k) -> HalfNat' n
  OddHalf'  : (k : Nat) -> (halvesNeq : n = k + S k) -> HalfNat' n

halfNat' : (n : Nat) -> HalfNat' n
halfNat' Z = EvenHalf' Z Refl
halfNat' (S Z) = OddHalf' Z Refl
halfNat' (S (S t)) = case halfNat' t of
                          EvenHalf' k prf => rewrite prf in
                                              rewrite plusSuccRightSucc k k in
                                                      EvenHalf' (S k) Refl
                          OddHalf' k prf =>
                                             rewrite prf in
                                             rewrite plusSuccRightSucc k (S k) in
                                                     OddHalf' (S k) Refl

-- But with such definition implementation of vectSplitHalf will be more
-- verbose. I need to rewrite xs type each time, when i use it.
vectSplitHalf' : {n : Nat} -> (xs : Vect n a) -> VectSplitHalf xs
vectSplitHalf' xs with (halfNat' n)
  vectSplitHalf' xs | EvenHalf' k halvesEq with (splitAt k {m = k} (rewrite sym halvesEq in xs)) proof 0 splitPrf
    _ | (left, right) =
        let prf = splitAppendEqSelf {k = k} {m = k} (rewrite sym halvesEq in xs)
         in rewrite prf in
            rewrite splitPrf in
            rewrite halvesEq in
                    VSplitEven left right
  vectSplitHalf' xs | OddHalf' k halvesNeq with (splitAt k {m = S k} (rewrite sym halvesNeq in xs)) proof 0 splitPrf
    _ | (left, right) =
        let prf = splitAppendEqSelf {k = k} {m = S k} (rewrite sym halvesNeq in xs)
         in rewrite prf in
            rewrite splitPrf in
            rewrite halvesNeq in
                    VSplitOdd left right

public export
data MySplitRecV : Vect n a -> Type where
  MyRecVNil : MySplitRecV []
  MyRecVOne : MySplitRecV [x]
  MyRecVPair : {n, m : Nat} -> (left : Vect n a) -> (right : Vect m a) ->
                    (MySplitRecV left) -> (MySplitRecV right) ->
                    MySplitRecV (left ++ right)

export
Eq (MySplitRecV xs) where
  _ == _ = True

export
mySplitRecV : {n : Nat} -> (xs : Vect n a) -> MySplitRecV xs
mySplitRecV [] = MyRecVNil
mySplitRecV [x] = MyRecVOne
mySplitRecV xs with (vectSplitHalf xs) proof splitPrf
  mySplitRecV (l ++ r) | VSplitEven l r =
    let res = MyRecVPair l r (mySplitRecV l) (mySplitRecV r)
    in res
  mySplitRecV (l ++ r) | VSplitOdd l r =
    let res = MyRecVPair l r (mySplitRecV l) (mySplitRecV r)
    in res

export
mergeSort : Ord a => {k : Nat} -> (xs : Vect k a) -> Vect k a
mergeSort xs with 1 (mySplitRecV xs)
  mergeSort [] | MyRecVNil = []
  mergeSort [x] | MyRecVOne = [x]
  mergeSort (l ++ r) | MyRecVPair l r lrec rrec =
    merge (mergeSort l | lrec) (mergeSort r | rrec)

-- Ex 10.2.3
divHalf : (n : Nat) -> Nat
divHalf Z = Z
divHalf (S Z) = Z
divHalf (S (S t)) = S (divHalf t)

divHalfLteSelf : (x : Nat) -> divHalf x `LTE` x
divHalfLteSelf Z = LTEZero
divHalfLteSelf (S Z) = LTEZero
divHalfLteSelf (S (S k)) = let rec = divHalfLteSelf k in LTESucc (lteSuccRight rec)

even : (n : Nat) -> Bool
even Z = True
even (S Z) = False
even (S (S k)) = even k

divEven : (n : Nat) -> (0 prf : even n = True) -> divHalf n + divHalf n = n
divEven Z _ = Refl
divEven (S Z) _ impossible
divEven (S (S k)) prf = let r = divEven k prf in
                             rewrite sym (plusSuccRightSucc (divHalf k) (divHalf k)) in
                             rewrite r in
                                     Refl

divOdd : (n : Nat) -> (0 prf : even n = False) -> S (divHalf n + divHalf n) = n
divOdd Z _ impossible
divOdd (S Z) _ = Refl
divOdd (S (S k)) prf = let r = divOdd k prf in
                            rewrite sym (plusSuccRightSucc (divHalf k) (divHalf k)) in
                            rewrite r in
                                    Refl

data MyHalfRec : Nat -> Type where
  MyHalfRecZ : MyHalfRec 0
  MyHalfRecEven : (n : Nat) -> (rec : Lazy (MyHalfRec n)) -> MyHalfRec (n + n)
  MyHalfRecOdd : (n : Nat) -> (rec : Lazy (MyHalfRec n)) -> MyHalfRec (S (n + n))

export
myHalfRec : (n : Nat) -> MyHalfRec n
myHalfRec Z = MyHalfRecZ
myHalfRec n with (even n) proof 0 prf
  _ | True = let r = MyHalfRecEven (divHalf n) (myHalfRec (divHalf n))
             in  rewrite sym (divEven n prf) in r
  _ | False = let r = MyHalfRecOdd (divHalf n) (myHalfRec (divHalf n))
              in  rewrite sym (divOdd n prf) in r

export
toListHalfRecMy : MyHalfRec n -> List Nat
toListHalfRecMy MyHalfRecZ = []
toListHalfRecMy (MyHalfRecEven n rec) = n :: toListHalfRecMy rec
toListHalfRecMy (MyHalfRecOdd n rec) = n :: toListHalfRecMy rec

export
toListHalfRec : HalfRec n -> List Nat
toListHalfRec HalfRecZ = []
toListHalfRec (HalfRecEven n rec) = n :: toListHalfRec rec
toListHalfRec (HalfRecOdd n rec) = n :: toListHalfRec rec

export
toBinary : (n : Nat) -> String
toBinary n with (myHalfRec n)
  toBinary 0 | MyHalfRecZ = ""
  toBinary _ | MyHalfRecOdd half rec = (toBinary half | rec) ++ "1"
  toBinary _ | MyHalfRecEven half rec = (toBinary half | rec) ++ "0"

-- Ex 10.2.4
public export
data MyVList : List a -> Type where
  MyVNil : MyVList []
  MyVOne : MyVList [x]
  MyVCons : {x, y : a} -> {xs : List a} -> (rec : Lazy (MyVList xs)) -> MyVList (x :: (xs ++ [y]))

-- For tests.
export
Eq (MyVList xs) where
  _ == _ = True

succLengthEqAppend : (xs : List a) -> (x : a) ->  S (length xs) = length (xs ++ [x])
succLengthEqAppend [] _ = Refl
succLengthEqAppend (y::xs') x = rewrite (succLengthEqAppend xs' x) in Refl

-- If i'd have a list split in half, i can easily construct VList.
total
myVListHelper : (sl : SnocList a) -> (rs : List a) -> {zs : List a} -> (acc : MyVList zs) ->
                 {auto prf : length sl = length rs} ->
                 MyVList (sl <>> (zs ++ rs))
myVListHelper Lin [] acc = rewrite appendNilRightNeutral zs in acc
myVListHelper (sl' :< l) [] acc impossible
myVListHelper (sl':<l) (r::rs') acc =
  let rec = myVListHelper sl' rs' (MyVCons {x = l} {y = r} acc) {prf = injective prf}
  in  rewrite appendAssociative zs [r] rs' in rec

-- I don't need SnocList view here, regualar 'SnocList a' is enough. But
-- anyway, here is the version with 'SnocList ls'.
total
myVListHelper' : (sl : SnocList ls) -> (rs : List a) -> {zs : List a} -> (acc : MyVList zs) ->
                {auto prf : length ls = length rs} ->
                MyVList (ls ++ zs ++ rs)
myVListHelper' Empty [] acc = rewrite appendNilRightNeutral zs in acc
myVListHelper' (Snoc y ls' _) [] acc =
  let r : S (length ls') === 0
      r = rewrite succLengthEqAppend ls' y in prf
    in absurd r
myVListHelper' (Snoc y ls' lrec) (r::rs') acc =
  let
      recPrf : length ls' === length rs'
      recPrf = injective {f = S} (rewrite succLengthEqAppend ls' y in prf)
      rec = myVListHelper' lrec rs' (MyVCons {x = y} {y = r} acc) {prf = recPrf}
  in rewrite appendAssociative zs [r] rs' in
     rewrite sym (appendAssociative ls' [y] ((zs ++ [r]) ++ rs')) in
             rec

-- But to use such helper i need a view, which splits a list in half
-- providing proofs, that halves are indeed equal (and center element, if list
-- has odd number of elements). Then i may use 'snocList' or fish (<><) to
-- convert left half of a list into either one of the SnocList types and call
-- corresponding helper.

-- Not used.
maxPrefix : (n : Nat) -> (xs : List a) -> (xs : (List a) ** LTE (length xs) n)
maxPrefix Z _ = ([] ** LTEZero)
maxPrefix (S n) [] = ([] ** LTEZero)
maxPrefix (S n) (x::xs') =
  let (rs ** lte) = maxPrefix n xs'
    in (x::rs ** LTESucc lte)

-- Slightly different of the one from exercise 10.1.
data TakeN2 : Nat -> List a -> Type where
  Fewer2 : {xs : List a} -> {prf : LTE (S (length xs)) n} -> TakeN2 n xs
  Exact2 : (n_xs : List a) -> (rest : List a) -> {prf : n = length n_xs} -> TakeN2 n (n_xs ++ rest)

total
takeN2 : (n : Nat) -> (xs : List a) -> TakeN2 n xs
takeN2 Z xs = Exact2 [] xs {prf = Refl}
takeN2 (S k) [] = Fewer2 {prf = LTESucc LTEZero}
takeN2 (S k) (x::xs') =
  case takeN2 k xs' of
       Fewer2 {prf = lte} => Fewer2 {prf = LTESucc lte}
       Exact2 n_xs rest {prf = eq} => Exact2 (x::n_xs) rest {prf = cong S eq}

-- View providing proofs, that list are indeed split into halves. See "Side
-- note" below.
public export
data Half : List a -> Type where
  Halves : (left : List a) -> (center : List a) -> (right : List a) ->
           {auto leftEqRight : length left = length right} ->
           {auto centerPrf : LTE (length center) 1} ->
           Half (left ++ center ++ right)

-- For tests.
export
Eq (Lib.Half ls) where
  _ == _ = True

-- Not used, the same as `succNotLTEpred`.
succLteSelf : {n : Nat} -> Not (LTE (S n) n)
succLteSelf LTEZero impossible
succLteSelf (LTESucc lte) = succLteSelf lte

-- Not used, the same as `lengthDistributesOverAppend`.
sumLengthEqLengthOfSum : (xs, ys : List a) -> length xs + length ys = length (xs ++ ys)
sumLengthEqLengthOfSum [] ys = Refl
sumLengthEqLengthOfSum (x::xs') ys = let rec = sumLengthEqLengthOfSum xs' ys in cong S rec

divHalfEqZ : {1 n : Nat} -> divHalf n = 0 -> LT n 2
divHalfEqZ {n = Z} _ = LTESucc LTEZero
divHalfEqZ {n = S Z} _ = LTESucc (LTESucc LTEZero)
divHalfEqZ {n = S (S Z)} _ impossible

divHalfEqSelf : {1 n : Nat} -> divHalf n = n -> n = Z
divHalfEqSelf {n = Z} prf = Refl
divHalfEqSelf {n = S Z} prf impossible
divHalfEqSelf {n = S (S k)} prf =
  let succLtePred : S k `LTE` k
      succLtePred = rewrite sym (injective prf) in divHalfLteSelf k
    in void (succNotLTEpred succLtePred)

divHalfSum : (1 a, b : Nat) -> divHalf (a + b) = a -> (k : Fin 2 ** b = a + finToNat k)
divHalfSum Z Z prf = (0 ** Refl)
divHalfSum Z (S Z) prf = (1 ** Refl)
divHalfSum Z (S (S _)) prf impossible
divHalfSum (S k) Z prf =
  -- I can't rewrite t2's type trivially to use `prf` as proof, because
  -- `plusZeroRightNeutral` rewrites _both_ sides of equality, but `prf` has
  -- `plus k 0` only on the left side.
  let t2 : divHalf (S k) === S k
      -- One approach in this case would be to use `prf` as rewrite rule and
      -- rewrite everything down to `Refl`.
      t2 = rewrite sym (plusZeroRightNeutral k) in
           rewrite prf in
           rewrite plusZeroRightNeutral k in
                   Refl
      t : S k = 0
      t = divHalfEqSelf {n = S k} t2
  in absurd t
-- Or i may not use `divHalfEqSelf` at all and write entire proof here.
--divHalfSum (S Z) Z prf impossible
--divHalfSum (S (S k)) Z prf =
--  let
--      succLtePred : LTE (S k) k
--      succLtePred = rewrite sym (injective prf) in
--                    rewrite plusZeroRightNeutral k in
--                            divHalfLteSelf k
--  in  void (succNotLTEpred succLtePred)
divHalfSum (S k) (S t) prf =
  let
      t2 : S (divHalf (plus k t)) === S k
      t2 = rewrite sym prf in
           rewrite sym (plusSuccRightSucc k t) in
                   Refl
      recPrf : divHalf (k + t) === k
      recPrf = injective {f = S} t2
      rec = divHalfSum k t recPrf
  in  case rec of (k ** kPrf) => (k ** cong S kPrf)

export
total
halfList : (xs : List a) -> Half xs
halfList xs with (takeN2 (divHalf (length xs)) xs)
  _ | Fewer2 {prf = lte} =
    let succLtePred : LTE (S (length xs)) (length xs)
        succLtePred = transitive lte (divHalfLteSelf (length xs))
    in  void (succNotLTEpred succLtePred)
  halfList (n_xs ++ rest) | Exact2 n_xs rest {prf = nxsLenPrf} =
    let prf' : divHalf (length n_xs + length rest) === length n_xs
        prf' = rewrite sym (lengthDistributesOverAppend n_xs rest) in nxsLenPrf
      in case divHalfSum (length n_xs) (length rest) prf' of
              (FZ ** eqPrf) =>
                           let leftEqRight : length n_xs === length rest
                               leftEqRight = rewrite sym (plusZeroRightNeutral (length n_xs)) in
                                                     sym eqPrf
                           in  Halves n_xs [] rest
                                        {leftEqRight = leftEqRight}
                                        {centerPrf = LTEZero}
              ((FS FZ) ** succPrf) =>
                    case rest of
                         [] => let neq : 0 === S (plus (length n_xs) Z)
                                   neq = rewrite plusSuccRightSucc (length n_xs) Z in succPrf
                               in  absurd neq
                         (r::rs') =>
                           let leftEqRight : S (length n_xs) === S (length rs')
                               leftEqRight = rewrite sym (plusZeroRightNeutral (length n_xs)) in
                                             rewrite plusSuccRightSucc (length n_xs) Z in
                                                     sym succPrf
                               -- Alternatively, just rewrite to Refl.
                               --leftEqRight = rewrite succPrf in
                               --              rewrite sym (plusSuccRightSucc (length n_xs) Z) in
                               --              rewrite plusZeroRightNeutral (length n_xs) in
                               --                      Refl
                           in  Halves n_xs [r] rs'
                                        {leftEqRight = injective leftEqRight}
                                        {centerPrf = LTESucc LTEZero}

-- Writing vList for helper using 'SnocList ls' view appears to be much
-- easier..
export
myVList' : (xs : List a) -> MyVList xs
myVList' xs with (halfList xs)
  myVList' (l ++ [] ++ r)  | Halves l [] r {leftEqRight = leftEqRight} {centerPrf = LTEZero} =
    myVListHelper' (snocList l) r MyVNil {prf = leftEqRight}
  myVList' (l ++ [c] ++ r) | Halves l [c] r {leftEqRight = leftEqRight} {centerPrf = LTESucc LTEZero} =
    myVListHelper' (snocList l) r MyVOne {prf = leftEqRight}
  myVList' (l ++ (c1::c2::cs) ++ r) | Halves l (c1::c2::cs) r {centerPrf = LTESucc lte} impossible

-- But for calling 'SnocList a' helper i need some additional proofs about
-- fish (<><) and chips (<>>) operations.

-- Not used.
fishLengthEqSum : (sx : SnocList a) -> (ys : List a) ->
      length (sx <>< ys) = length sx + length ys
fishLengthEqSum sx [] = rewrite plusZeroRightNeutral (length sx) in Refl
fishLengthEqSum sx (y::ys') =
  let rec = fishLengthEqSum (sx :< y) ys'
  in  rewrite sym (plusSuccRightSucc (length sx) (length ys')) in rec

fishSnocLengthEqSucc : (sx : SnocList a) -> (z : a) -> (ys : List a) ->
      length ((sx :< z) <>< ys) = S (length (sx <>< ys))
fishSnocLengthEqSucc sx z [] = Refl
fishSnocLengthEqSucc sx z (y::ys') =
  let rec  = fishSnocLengthEqSucc (sx :< z) y ys'
      elimZ = fishSnocLengthEqSucc sx z ys'
      elimY = fishSnocLengthEqSucc sx y ys'
  in rewrite rec in rewrite elimZ in rewrite elimY in Refl

fishNilLengthNeutral : (xs : List a) -> length ([<] <>< xs) = length xs
fishNilLengthNeutral [] = Refl
fishNilLengthNeutral (x::xs') =
  let rec = fishNilLengthNeutral xs'
      prf = fishSnocLengthEqSucc Lin x xs'
  in rewrite sym rec in rewrite prf in Refl

chipsDistributesOverAppend : (sx : SnocList a) -> (ys, zs : List a) ->
                            sx <>> (ys ++ zs) = (sx <>< ys) <>> zs
chipsDistributesOverAppend sx [] zs = Refl
chipsDistributesOverAppend sx (y::ys') zs =
  let rec = chipsDistributesOverAppend (sx:<y) ys' zs
    in rewrite rec in Refl

export
myVList : (xs : List a) -> MyVList xs
myVList xs with (halfList xs)
  myVList (ls ++ [] ++ rs)  | Halves ls [] rs {leftEqRight = leftEqRight} {centerPrf = LTEZero} =
    let h = myVListHelper (Lin <>< ls) rs MyVNil
              {prf = rewrite fishNilLengthNeutral ls in leftEqRight}
    in rewrite chipsDistributesOverAppend Lin ls rs in h
  myVList (ls ++ [c] ++ rs) | Halves ls [c] rs {leftEqRight = leftEqRight} {centerPrf = LTESucc LTEZero} =
    let h = myVListHelper (Lin <>< ls) rs (MyVOne {x = c})
              {prf = rewrite fishNilLengthNeutral ls in leftEqRight}
    in rewrite chipsDistributesOverAppend Lin ls (c::rs) in h
  myVList (ls ++ (c1::c2::cs) ++ rs) | Halves ls (c1::c2::cs) rs {centerPrf = LTESucc lte} impossible

export
palindrome : Eq a => (xs : List a) -> Bool
palindrome xs with (myVList xs)
  palindrome [] | MyVNil = True
  palindrome [x] | MyVOne = True
  palindrome (x::(xs' ++ [y])) | MyVCons rec =
    if x == y
       then (palindrome xs' | rec)
       else False


-- Side note:
-- I use arguments in type constructors for implementing constraints, which
-- will be solved _automatically_ during type check. Notably, i can't aid
-- Idris directly to solve them, because it'll do this fully on its own.
data T : List a -> Nat -> Type where
  MkT : (l : List a) -> T l (length l)

f : (xs : List a) -> T l 2 -> Int
-- This definition does not compile, because the 2nd argument may be only of
-- type `T l 2`, but `MkT l` may construct arguments of different type as
-- well. Or in other words, because Idris can't deduce, that `length l`
-- equals to 2.
--f xs (MkT l) = ?z2
-- This definition will compile though, because `length [x1, x2]` equals to 2.
f xs (MkT [x1,x2]) = ?f_body

-- Or i may pattern-match on constructor fields to make constraint solveable.
total
f' : (xs : List a) -> T xs 2 -> Int
f' [] (MkT []) impossible
f' [x1] (MkT [x1]) impossible
f' [x1, x2] (MkT [x1,x2]) = ?f'_body
f' (x1::x2::x3::xs) (MkT (x1::x2::x3::xs)) impossible

-- And i use value arguments of data constructors, when i want to _provide_ a
-- proof for something. So, if i want to provide a proof for constraint in
-- type, i should, first, relax this contraint, so Idris can trivially solve
-- it (e.g. make it to be just a type variable), and then provide proof of
-- some property of this type variable as a value argument.
data T2 : List a -> Nat -> Type where
  MkT2 : (l : List a) -> {auto prf : n = length l} -> T2 l n

-- Here, `prf` is the proof of constraint `2 = length l`. And i can manipulate
-- this proof in a usual way.
f2 : (xs : List a) -> T2 l 2 -> Int
f2 xs (MkT2 l {prf = prf}) = ?f2_body

-- But now pattern-matching on constructor fields has no sense, because here
-- 'prf' will be trivial proof of '2 = 2', which is useless.
total
f2' : (xs : List a) -> T2 xs 2 -> Int
f2' [] (MkT2 [] {prf = prf}) impossible
f2' [x] (MkT2 [x] {prf = prf}) impossible
f2' [x1,x2] (MkT2 [x1,x2] {prf = prf}) = ?f2'_body
f2' (x1::x2::x3::xs) (MkT2 (x1::x2::x3::xs) {prf = prf}) impossible





-- Not used.
consNonEmpty : NonEmpty xs -> NonEmpty (x::xs)
consNonEmpty IsNonEmpty = IsNonEmpty

snocNonEmpty : (xs : List a) -> (y : a) -> NonEmpty (xs ++ [y])
snocNonEmpty [] y = IsNonEmpty
snocNonEmpty (x::_) _ = IsNonEmpty

total
tailAppendAssoc : (xs : List a) -> (y : a) ->
                  {auto 0 _ : NonEmpty xs} ->
                  {auto 0 _ : NonEmpty (xs ++ [y])} ->
                  tail (xs ++ [y]) = tail xs ++ [y]
tailAppendAssoc [] _ impossible
tailAppendAssoc (x::xs) y = Refl

total
snocListTail : {xs : List a} -> {auto 0 prf : NonEmpty xs} -> SnocList xs -> SnocList (tail xs)
snocListTail Empty impossible
snocListTail (Snoc _ [] Empty) = Empty
snocListTail (Snoc y (xs' ++ [y']) rec@(Snoc _ _ _)) =
  let prf = snocNonEmpty xs' y'
      r = snocListTail rec
      in rewrite tailAppendAssoc (xs'++[y']) y in
                 Snoc y (tail (xs' ++ [y'])) r

-- Just for lulz.
finRefl : {x, n : Nat} -> {lt : LT x n} -> x = finToNat (the (Fin n) (natToFinLT x))
finRefl {x = Z} {n = Z} {lt = lt} impossible
finRefl {x = Z} {n = S t} {lt = LTESucc LTEZero} = Refl
finRefl {x = S k} {n = Z} {lt = lt} impossible
finRefl {x = S k} {n = S t} {lt = LTESucc lt} =
  let rec = finRefl {x = k} {n = t} {lt = lt}
  in rewrite sym rec in Refl

