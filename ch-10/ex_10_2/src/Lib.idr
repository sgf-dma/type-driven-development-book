module Lib

import Data.Nat
import Data.Nat.Views
import Data.Fin
import Data.List
import Data.List.Views
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

-- Ex 10.2.3
data MyHalfRec : Nat -> Type where
  MyHalfRecZ : MyHalfRec 0
  MyHalfRecEven : (n : Nat) -> (rec : Lazy (MyHalfRec n)) -> MyHalfRec (n + n)
  MyHalfRecOdd : (n : Nat) -> (rec : Lazy (MyHalfRec n)) -> MyHalfRec (S (n + n))

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

divEven : (n : Nat) -> (prf : even n = True) -> divHalf n + divHalf n = n
divEven Z _ = Refl
divEven (S Z) _ impossible
divEven (S (S k)) prf = let r = divEven k prf in
                             rewrite sym (plusSuccRightSucc (divHalf k) (divHalf k)) in
                             rewrite r in
                                     Refl

divOdd : (n : Nat) -> (prf : even n = False) -> S (divHalf n + divHalf n) = n
divOdd Z _ impossible
divOdd (S Z) _ = Refl
divOdd (S (S k)) prf = let r = divOdd k prf in
                            rewrite sym (plusSuccRightSucc (divHalf k) (divHalf k)) in
                            rewrite r in
                                    Refl

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
data MyVList : List a -> Type where
  MyVNil : MyVList []
  MyVOne : MyVList [x]
  MyVCons : {0 x : a} -> {0 y : a} -> (rec : MyVList xs) -> MyVList (x :: (xs ++ [y]))

succLengthEqAppend : (xs : List a) -> (x : a) ->  S (length xs) = length (xs ++ [x])
succLengthEqAppend [] _ = Refl
succLengthEqAppend (y::xs') x = rewrite (succLengthEqAppend xs' x) in Refl

-- FIXME: Do i need SnocList view or just regular SnocList?
total
myVListHelper : (sl : SnocList ls) -> (rs : List a) -> (acc : MyVList zs) ->
                {auto prf : length ls = length rs} ->
                MyVList (ls ++ zs ++ rs)
myVListHelper Empty [] acc = rewrite appendNilRightNeutral zs in acc
myVListHelper (Snoc y ls' _) [] acc =
  let r : S (length ls') === 0
      r = rewrite succLengthEqAppend ls' y in prf
    in absurd r
myVListHelper (Snoc y ls' lrec) (r::rs') acc =
  let
      recPrf : length ls' === length rs'
      recPrf = injective {f = S} (rewrite succLengthEqAppend ls' y in prf)
      rec = myVListHelper lrec rs' (MyVCons {x = y} {y = r} acc) {prf = recPrf}
  in rewrite appendAssociative zs [r] rs' in
     rewrite sym (appendAssociative ls' [y] ((zs ++ [r]) ++ rs')) in
             rec

total
myVListHelper3 : (sl : SnocList a) -> (rs : List a) -> (acc : MyVList zs) ->
                 {auto prf : length sl = length rs} ->
                 MyVList (sl <>> (zs ++ rs))
myVListHelper3 Lin [] acc = rewrite appendNilRightNeutral zs in acc
myVListHelper3 (sl' :< l) [] acc impossible
myVListHelper3 (sl':<l) (r::rs') acc =
  let rec = myVListHelper3 sl' rs' (MyVCons {x = l} {y = r} acc) {prf = injective prf}
  in  rewrite appendAssociative zs [r] rs' in rec



{-
myVListHelper2 : (xs : List a) ->
                 (List a, DPair (SnocList a, List a) (\(xs, ys) => length xs === length ys))
myVListHelper2 [] = ([], ((Lin, []) ** Refl))
myVListHelper2 [x] = ([x], ((Lin, []) ** Refl))
myVListHelper2 (x1::x2::xs) =
  let (center, ((ls, rs) ** prf)) = myVListHelper2 xs
  in  ?w3
  -}

maxPrefix : (n : Nat) -> (xs : List a) -> (xs : (List a) ** LTE (length xs) n)
maxPrefix Z _ = ([] ** LTEZero)
maxPrefix (S n) [] = ([] ** LTEZero)
maxPrefix (S n) (x::xs') =
  let (rs ** lte) = maxPrefix n xs'
    in (x::rs ** LTESucc lte)

-- Slightly different variant from exercise 10.1.
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
data Half : List a -> Type where
  Halves : (left : List a) -> (center : List a) -> (right : List a) ->
           -- FIXME: Why right = left? Why not vice versa?
           {auto leftEqRight : length left = length right} ->
           {auto centerPrf : LTE (length center) 1} ->
           Half (left ++ center ++ right)


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







myVList4 : (xs : List a) -> MyVList xs
myVList4 xs with (halfList xs)
  myVList4 (l ++ [] ++ r)  | Halves l [] r {leftEqRight = leftEqRight} {centerPrf = LTEZero} =
    myVListHelper (snocList l) r MyVNil {prf = leftEqRight}
  myVList4 (l ++ [c] ++ r) | Halves l [c] r {leftEqRight = leftEqRight} {centerPrf = LTESucc LTEZero} =
    myVListHelper (snocList l) r MyVOne {prf = leftEqRight}
  myVList4 (l ++ (c1::c2::cs) ++ r) | Halves l (c1::c2::cs) r {centerPrf = LTESucc lte} impossible

ss2 : (sx : SnocList a) -> (ys : List a) ->
      length (sx <>< ys) = length sx + length ys
ss2 Lin [] = ?b1
ss2 Lin (y::ys') = ?b2
ss2 (sx':<x) [] = ?b3
ss2 (sx':<x) (y::ys') =
  let r1 = ss2 sx' ys'
  in  ?b4

snocTransitive : (sx : SnocList a) -> (x : a) -> (ys : List a) -> (sx :< x) <>< ys = sx <>< (x::ys)
snocTransitive sx x [] = Refl
snocTransitive sx x (y::ys') = Refl

sss : (sx : SnocList a) -> (z : a) -> (ys : List a) ->
      length ((sx :< z) <>< ys) = S (length (sx <>< ys))
sss sx z [] = Refl
sss sx z (y::ys') =
  let rec = sss (sx :< z) y ys'
      recZ = sss sx z ys'
      recY = sss sx y ys'
  in rewrite rec in rewrite recZ in rewrite recY in Refl

snocNilLength : (xs : List a) -> length ([<] <>< xs) = length xs
snocNilLength [] = Refl
snocNilLength (x::xs') =
  let rec = snocNilLength xs'
      rrr = sss Lin x xs'
  in rewrite sym rec in rewrite rrr in Refl

snocDistributesOverAppend : (sx : SnocList a) -> (ys, zs : List a) ->
                            sx <>> (ys ++ zs) = (sx <>< ys) <>> zs
snocDistributesOverAppend sx [] zs = Refl
snocDistributesOverAppend sx (y::ys') zs =
  let rec = snocDistributesOverAppend (sx:<y) ys' zs
    in rewrite rec in Refl

myVList3 : (xs : List a) -> MyVList xs
myVList3 xs with (halfList xs)
  myVList3 (ls ++ [] ++ rs)  | Halves ls [] rs {leftEqRight = leftEqRight} {centerPrf = LTEZero} =
    let h = myVListHelper3 (Lin <>< ls) rs MyVNil {prf = rewrite snocNilLength ls in leftEqRight}
        ppp = snocDistributesOverAppend Lin ls rs
    in rewrite ppp in h
  myVList3 (ls ++ [c] ++ rs) | Halves ls [c] rs {leftEqRight = leftEqRight} {centerPrf = LTESucc LTEZero} =
    let h = myVListHelper3 (Lin <>< ls) rs (MyVOne {x = c}) {prf = rewrite snocNilLength ls in leftEqRight}
        ppp = snocDistributesOverAppend Lin ls (c::rs)
    in rewrite ppp in h
  myVList3 (ls ++ (c1::c2::cs) ++ rs) | Halves ls (c1::c2::cs) rs {centerPrf = LTESucc lte} impossible

--myVList5 : (xs : List a) -> MyVList xs
--myVList5 xs with (halfList xs) proof 0 halfPrf2
--  myVList5 (l ++ c ++ r)  | Halves2 l c r {leftEqRight = leftEqRight} {centerPrf = LTEZero} = ?z1

--myVListHelper4 : (xs : List a) -> Int
--myVListHelper4 xs with (halfList xs) proof 0 halfPrf
--  myVListHelper4 (l ++ c ++ r) | Halves l c r {lrEqPrf = lrEqPrf} {centerPrf = centerPrf} = ?z1





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
finRefl : {0 lt : LT x n} -> x = finToNat (the (Fin n) (natToFinLT x))

