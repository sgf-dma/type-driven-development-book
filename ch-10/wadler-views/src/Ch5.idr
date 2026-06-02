
module Ch5

import Data.Nat
import Data.List
import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Decidable.Equality
import Syntax.PreorderReasoning

import Remainder
import SnocVect

-- 5.Viewing a list backwards

-- Note the difference from 'Data.List.Views.SnocList': this one is not
-- recursive and type parameter is not a List, but list element's type.
data MySnocList : Type -> Type where
  MyNilSnoc : MySnocList a
  MySnoc : (rest : List a) -> (x : a) -> MySnocList a

-- Full list traversal, linear time.
mySnocList : List a -> MySnocList a
mySnocList [] = MyNilSnoc
mySnocList (x::xs) =
  case mySnocList xs of
       MyNilSnoc => MySnoc [] x
       MySnoc rest x' => MySnoc (x::rest) x'

-- Full list traversal, linear time.
mySnocOut : MySnocList a -> List a
mySnocOut MyNilSnoc = []
mySnocOut (MySnoc [] x') = [x']
mySnocOut (MySnoc (x::xs) x') = x::(mySnocOut (MySnoc xs x'))

-- This view does not provide any clues about original pattern.
myLast : (xs : List a) -> a
myLast xs with (mySnocList xs)
  _ | MyNilSnoc = ?undefLast
  _ | MySnoc xs' x = x

-- Rotate list to the right. One full list traversal.
export
rotright : List a -> List a
rotright xs = case (mySnocList xs) of
                   MyNilSnoc => []
                   MySnoc rest x => x::rest

-- Rotate to the right by 2 elements. Two full list traversals (in `mySnocList`).
export
rotright2 : List a -> List a
rotright2 xs = case (mySnocList xs) of
                   MyNilSnoc => []
                   MySnoc rest x =>
                        -- Traverse entire 'rest' again.
                        case mySnocList rest of
                             MyNilSnoc => [x]
                             MySnoc rest' x' => x'::x::rest'

-- Rotate to the right by n elements. Traverses entire rest at each iteration.
export
rotrightN : (n : Nat) -> List a -> List a
rotrightN Z xs = xs
rotrightN (S t) xs = rotrightN t (rotright xs)
{-
rotrightN (S t) xs = case (mySnocList xs) of
                       MyNilSnoc => []
                       MySnoc rest x => rotrightN t (x::rest)
                       -}

-- Rotate list to the left. One full list traversal.
export
rotleft : List a -> List a
rotleft [] = []
rotleft (x::xs) = mySnocOut (MySnoc xs x)

-- Rotate to the left by 2 elements. Two full list traversals.
export
rotleft2 : List a -> List a
rotleft2 [] = []
rotleft2 (x::xs) = case xs of
                        [] => [x]
                        (x'::xs') => mySnocOut (MySnoc (mySnocOut (MySnoc xs' x)) x')

export
rotleftN : (n : Nat) -> List a -> List a
rotleftN Z xs = xs
rotleftN (S t) xs = rotleftN t (rotleft xs)

-- Recursive version of MySnocList. Still, type parameter is not a List, but
-- list element's type.
data MySnocListRec : Type -> Type where
  MyNilSnocRec : MySnocListRec a
  MySnocRec : (rest : MySnocListRec a) -> (x : a) -> MySnocListRec a

-- I can't use here the same trick as above in `mySnocList` with adding x to
-- the 'rest' part of `MySnocRec` constructor, because in `MySnoc` this 'rest'
-- part is built from head-to-tail (cons-ed), but here, in recursive view, the
-- 'rest' is built from tail-to-head (snoc-ed). Therefore, i need to send 'x'
-- to the very beginning of building the 'rest' value, i.e. i need accumulator.
mySnocListRec : (xs : List a) -> MySnocListRec a
mySnocListRec xs = go xs MyNilSnocRec
  where
    go : (xs : List a) -> (acc : MySnocListRec a) -> MySnocListRec a
    go [] acc = acc
    go (x::xs') acc = go xs' (MySnocRec acc x)

-- The same note here: i can't use the trick from `mySnocOut` here, because
-- 'rest' is built from tail-to-head (snoc-ed). Therefore, i need accumulator.
mySnocOutRec : MySnocListRec a -> List a
mySnocOutRec sx = go sx []
  where
    go : MySnocListRec a -> (acc : List a) -> List a
    go MyNilSnocRec acc = acc
    go (MySnocRec rest x) acc = go rest (x::acc)

-- This view also does not provide any clues about original pattern.
myLastRec : (xs : List a) -> a
myLastRec xs with (mySnocListRec xs)
  _ | MyNilSnocRec = ?undefLastRec
  _ | MySnocRec _ x = x

-- This implementation is worse, than Wadler's 'rotright', because here i
-- traverse list twice: first to build MySnocListRec, then to rebuild it again
-- into list. But Wadler's version does need a rebuild phase, because 'rest'
-- is already a list.
export
rotrightRec : (xs : List a) -> List a
rotrightRec xs = case (mySnocListRec xs) of
                   MyNilSnocRec => []
                   MySnocRec rest x => x::(mySnocOutRec rest)

-- But here is the difference: i don't need to traverse 'rest' again to obtain
-- second from last element and i traverse list twice no matter how much i
-- rotate.
export
rotright2Rec : List a -> List a
rotright2Rec xs = case (mySnocListRec xs) of
                     MyNilSnocRec => []
                     MySnocRec rest x =>
                        case rest of
                             MyNilSnocRec => [x]
                             MySnocRec rest' x' => x'::x::(mySnocOutRec rest')

-- Therefore, if i rotate a long list by some big n, this implementation will
-- be more efficient, because it'll still need only 2 traversals: to build
-- MySnocListRec and to rebuild it again into list at the end.
total
export
rotrightNRec : (n : Nat) -> (xs : List a) -> List a
rotrightNRec n xs = go n [] (mySnocListRec xs)
  where
    go : (n : Nat) -> (acc : List a) -> (xs : MySnocListRec a) -> List a
    go Z acc xs = acc ++ (mySnocOutRec xs)
    go (S t) acc MyNilSnocRec =
      case mySnocListRec acc of
           MyNilSnocRec => []
           MySnocRec rest x => go t [x] rest
    go (S t) acc (MySnocRec rest x) = go t (x::acc) rest

{-
go2 : (n : Nat) -> (xs : List a) -> {lte : n `LTE` length xs} -> (acc : List a) -> List a
go2 Z xs acc = acc ++ xs
go2 (S t) (x::xs') acc {lte = LTESucc lte'} with (mySnocListRec (x::xs'))
  -- This is impossible case, but because `MySnocListRec` type does depend on
  -- list itself (as `SnocList` does), i can't deduce empty list from
  -- `MyNilSnocRec` constructor. And, as a consequence, `lte` argument is
  -- useless here, because i can't use it to prove impossible case (because i
  -- haven't proved, that `length xs = 0`)
  _ | MyNilSnocRec = ?go2_impossible
  go2 (S t) (x::xs') acc | MySnocRec rest z =
    let rec = (go2 t xs' (x::acc) | rest) in ?b1
    -}

total
rotrightNRec2Le : (n : Nat) -> (xs : List a) -> {auto lte : n `LTE` length xs} -> List a
rotrightNRec2Le n xs = go n xs [] {lte = lte}
  where
    go : (n : Nat) -> (xs : List a) -> {lte : n `LTE` length xs} -> (acc : List a) -> List a
    -- I use 'xs' only for 'lte' argument and for constructing view.
    go n xs acc {lte} with (mySnocListRec xs)
      -- 'MyNilSnocRec' doesn't refine 'xs' to [], because type 'MySnocListRec'
      -- does not depend on list itself (as 'SnocList' does). As a consequence
      -- 'lte' does not prove this case as impossible:
      --
      --    go (S t) [] acc {lte} | MyNilSnocRec impossible
      --
      -- (because i haven't proved, that `length xs = 0`) and, in fact, 'lte'
      -- argument is useless here at all. I.e. the only possible arguments here
      -- are:
      --
      --    go Z [] acc {lte} | MyNilSnocRec = acc ++ xs
      --
      -- but i can't prove it. Nevertheless, i still can implement this branch
      -- without any refining.
      go n _ acc {lte} | MyNilSnocRec = acc
      go Z _ acc {lte} | MySnocRec rec z = acc ++ mySnocOutRec rec ++ [z]
      go (S t) xs acc {lte = lte} | MySnocRec rec z =
        go t xs (z::acc) {lte = lteSuccLeft lte} | rec

export
rotrightNRec2 : (n : Nat) -> (xs : List a) -> List a
rotrightNRec2 n [] = []
rotrightNRec2 n (x::xs') =
  case findRemainder n (length (x::xs')) of
       MkRem _ r {prfR} => rotrightNRec2Le r (x::xs') {lte = lteSuccLeft prfR}

snocLength : (xs : List a) -> (z : a) -> length (xs ++ [z]) = S (length xs)
snocLength [] z = Refl
snocLength (x::xs') z = cong S (snocLength xs' z)

total
rotrightNRec3Le : (n : Nat) -> (xs : List a) -> {auto lte : n `LTE` length xs} -> List a
rotrightNRec3Le n xs = go n xs {lte = lte} []
  where
    go : (n : Nat) -> (xs : List a) -> {lte : n `LTE` length xs} -> (acc : List a) -> List a
    go n xs acc {lte} with (snocList xs)
      go Z [] acc {lte = LTEZero} | Empty = acc
      -- 'SnocList' constructor contains both original list version 'rest' and
      -- 'SnocList' version of 'rest' as 'rec'. Therefore, i don't need to undo
      -- snocList as i did in go2 with `mySnocOutRec`, i already have it in
      -- 'rest'.
      go Z (rest ++ [z]) acc {lte} | Snoc z rest _ = acc ++ rest ++ [z]
      -- This is impossible case, which i can't prove before with `MySnocListRec`.
      -- Now i can prove it, because `snocList` refines `xs` to [] and because i
      -- have `lte`, which has the type `lte : LTE (S t) 0` here.
      go (S t) [] acc {lte} | Empty impossible
      go (S t) (rest ++ [z]) acc {lte} | Snoc z rest rec =
        let ltePrf : LTE (S t) (S (length rest))
            ltePrf = rewrite sym (snocLength rest z) in lte
        in case ltePrf of LTESucc lte' => (go t rest (z::acc) {lte = lte'} | rec)

export
rotrightNRec3 : (n : Nat) -> (xs : List a) -> List a
rotrightNRec3 n [] = []
rotrightNRec3 n (x::xs') =
  case findRemainder n (length (x::xs')) of
       MkRem _ r {prfR} => rotrightNRec3Le r (x::xs') {lte = lteSuccLeft prfR}



-- This implementation is also worse, than Wadler's one, because Wadler has
-- only single full list traversal, but here is two.
export
rotleftRec : (xs : List a) -> List a
rotleftRec [] = []
rotleftRec (x::xs') = mySnocOutRec (MySnocRec (mySnocListRec xs') x)

-- So, here is an intresting difference: Wadler's version traverses full
-- list at each step of building MySnocList, but here i still traverse full
-- list only twice: first to build MySnocListRec, and then to rebuild it back
-- to list.
export
rotleft2Rec : (xs : List a) -> List a
rotleft2Rec [] = []
rotleft2Rec (x::xs') =
  case xs' of
       [] => [x]
       (x'::rest) => mySnocOutRec (MySnocRec (MySnocRec (mySnocListRec rest) x) x')

-- Here i also have 'MySnocListRec' value as in go of 'rotrightNRec' above,
-- but there, in rotright, i've been disassembling 'MySnocListRec' value
-- recursively and, therefore, i may have been interested in using recursive
-- view. But here i'm assembling 'MySnocListRec' value (i.e. it's an
-- accumulator), so recursive view does not help here. So, no version 2 here
-- and i'm going straight to version 3.
export
rotleftNRec : (n : Nat) -> (xs : List a) -> List a
rotleftNRec n xs = go n xs MyNilSnocRec
  where
    go : (n : Nat) -> (rest : List a) -> (acc : MySnocListRec a) -> List a
    go Z rest acc = rest ++ mySnocOutRec acc
    go (S n') [] acc = case mySnocOutRec acc of
                            [] => []
                            (x::xs') => go n' xs' (MySnocRec MyNilSnocRec x)
    go (S n') (x::xs') acc = go n' xs' (MySnocRec acc x)

rotleftNRec3Le : (n : Nat) -> (xs : List a) -> {auto 0 lte : n `LTE` length xs} -> List a
rotleftNRec3Le n xs {lte} = go n xs Empty {lte = lte}
  where
    go : (n : Nat) -> (xs : List a) -> {ys : List a} -> {0 lte : n `LTE` length xs} -> (acc : SnocList ys) -> List a
    go Z xs {ys} acc = xs ++ ys
    -- Note, that i don't need recursive argument in view here at all. So,
    -- effectively this version is equivalent to 'go' in 'rotleftNRec', except
    -- that version 1 accepts any 'n' and handles overflow by itself, but here
    -- overflow is handled by the caller.
    go (S n') (x::xs') {ys} acc {lte = LTESucc lte'} = go n' xs' (Snoc x ys acc) {lte = lte'}

export
rotleftNRec3 : (n : Nat) -> (xs : List a) -> List a
rotleftNRec3 n [] = []
rotleftNRec3 n (x::xs') =
  case findRemainder n (length (x::xs')) of
       MkRem _ r {prfR} => rotleftNRec3Le r (x::xs') {lte = lteSuccLeft prfR}

-- My variant of snocListHelp from Data.List.Views. Not used. Note the
-- difference: multiplicity of 'ys' is 0 in my version.
snocListHelp : (acc : SnocList ys) -> (xs : List a) -> SnocList (ys ++ xs)
snocListHelp acc [] = rewrite appendNilRightNeutral ys in acc
snocListHelp Empty (x::xs') = snocListHelp (Snoc x [] Empty) xs'
snocListHelp acc@(Snoc z rest _) (x::xs') =
  let r = Snoc x (rest ++ [z]) acc
  in rewrite appendAssociative (rest ++ [z]) [x] xs' in snocListHelp r xs'

-- Version for Vectors. Without limit on 'n', but using my 'SnocVect'. Compare
-- with 'rotrightNRec'.
export total
rotrightVecNRec : (n : Nat) -> (xs : Vect m a) -> Vect m a
rotrightVecNRec n xs0 = go n xs0 []
  where
    go : (n : Nat) -> {0 m : Nat} -> (xs : Vect m a) -> (acc : Vect k a) -> Vect (k + m) a
    go n {m = m'} xs {k} acc with (snocVect xs)
      go Z      {m = m'} xs {k} acc | _ = acc ++ xs
      go (S n') {m = Z} [] {k} acc | EmptyV with (snocVect acc)
        go (S n') {m = Z} [] {k = Z} [] | EmptyV | EmptyV = []
        go (S n') {m = Z} [] {k = k' + 1} (rest ++ [z]) | EmptyV | SnocV z rest rec =
          let prf : (k' + 1) + 0 === S k'
              prf = Calc $
                      |~ (k' + 1) + 0
                      ~~ k' + 1 ...(plusZeroRightNeutral (k' + 1))
                      ~~ S (k' + 0) ...(sym (plusSuccRightSucc k' 0))
                      ~~ S k'
                            ...(rewrite plusZeroRightNeutral k' in Refl)
          in  rewrite prf in (go n' rest [z] | rec)
      go (S n') {m = m' + 1} (rest ++ [z]) {k} acc | SnocV z rest rec =
        let result = (go n' rest (z::acc) | rec)
            prf : k + (m' + 1) === S (k + m')
            prf = Calc $
                    |~ k + (m' + 1)
                    ~~ k + S (m' + 0) ...(rewrite plusSuccRightSucc m' Z in Refl)
                    ~~ k + S m' ...(rewrite plusZeroRightNeutral m' in Refl)
                    ~~ S (k + m') ...(sym (plusSuccRightSucc k m'))
        in  rewrite prf in result

-- Version for Vectors with limit on 'n'. Compare with 'rotrightNRec3Le'.
rotrightVecNRec3Le : (n : Nat) -> (xs : Vect m a) -> {auto lte : n `LTE` m} -> Vect m a
rotrightVecNRec3Le n0 xs0 {lte = lte0} = go n0 xs0 [] {lte = lte0}
  where
    -- The same as above, but with limit on 'n'.
    go : (n : Nat) -> {0 m : Nat} -> (xs : Vect m a) -> {lte : n `LTE` m} -> (acc : Vect k a) -> Vect (k + m) a
    go n {m = m'} xs acc {lte = lte} with (snocVect xs)
      -- 'lte' allows to prove, that in this branch 'n === Z'
      --go Z {m = _} [] acc {lte = _} | EmptyV = rewrite plusZeroRightNeutral k in acc
      --go Z {m = _} xs@(rest ++ [z]) acc {lte = LTEZero} | SnocV z rest rec = acc ++ xs
      -- But in fact, i may combine this two cases into one:
      go Z {m = _} xs acc {lte = _} | _ = acc ++ xs
      go (S n') {m = m' + 1}    (rest ++ [z]) acc {lte = lte} | SnocV z rest rec =
        let lteR : LTE (S n') (S m')
            lteR = rewrite sym (plusZeroRightNeutral m') in
                   rewrite plusSuccRightSucc m' 0 in
                           lte
        in  case lteR of
                 LTESucc lte' =>
                   let result = (go n' rest (z::acc) {lte = lte'} | rec)
                       prf : k + (m' + 1) === S (k + m')
                       prf = Calc $
                               |~ k + (m' + 1)
                               ~~ k + S (m' + 0)
                                     ...(rewrite plusSuccRightSucc m' Z in Refl)
                               ~~ k + S m'
                                     ...(rewrite plusZeroRightNeutral m' in Refl)
                               ~~ S (k + m')
                                     ...(sym (plusSuccRightSucc k m'))
                    in rewrite prf in result


-- Note, that if i want to leave multiplicity of 'm' zero, i need a proof of
-- `length xs' === m'`.
export
rotrightVecNRec3 : (n : Nat) -> (xs : Vect m a) -> Vect m a
rotrightVecNRec3 n [] = []
rotrightVecNRec3 n {m = S m'} (x::xs') =
  case findRemainder n (length (x::xs')) of
       MkRem _ r {prfR} => rotrightVecNRec3Le r (x::xs')
                            {lte = rewrite sym (lengthCorrect xs') in lteSuccLeft prfR}

-- Otherwise, using non-linear 'm', i may simplify 'lte' proof.
rotrightVecNRec3' : {m : Nat} -> (n : Nat) -> (xs : Vect m a) -> Vect m a
rotrightVecNRec3' n [] = []
rotrightVecNRec3' n {m = S m'} (x::xs') =
  case findRemainder n (S m') of
       MkRem _ r {prfR} => rotrightVecNRec3Le r (x::xs') {lte = lteSuccLeft prfR}
-- Compare with 'rotleftNRec'.
export
rotleftVecNRec : (n : Nat) -> (xs : Vect m a) -> Vect m a
rotleftVecNRec n xs0 = rewrite sym (plusZeroRightNeutral m) in go n xs0 [] EmptyV
  where
    go : (n : Nat) -> {0 m : Nat} -> (xs : Vect m a) -> (ys : Vect k a) -> (acc : SnocVect ys) -> Vect (m + k) a
    go Z xs ys _ = xs ++ ys
    go (S n') [] [] _ = []
    go (S n') [] {k = S k'} (y::ys') _ = rewrite sym (plusZeroRightNeutral k') in
                                         rewrite plusSuccRightSucc k' 0 in
                                                 go n' ys' [y] (SnocV y [] EmptyV)
    go (S n') {m = S m'} (x::xs') {k = k} ys acc =
      let prf : S (m' + k) === m' + (k + 1)
          prf = Calc $
                  |~ S (m' + k)
                  ~~ m' + S k
                        ...(plusSuccRightSucc m' k)
                  ~~ m' + S (k + Z)
                        ...(rewrite plusZeroRightNeutral k in Refl)
                  ~~ m' + (k + 1)
                        ...(rewrite plusSuccRightSucc k Z in Refl)
        in rewrite prf in go n' xs' _ (SnocV x ys acc)

-- Compare with 'rotleftNRec3Le'.
rotleftVecNRec3Le : (n : Nat) -> (xs : Vect m a) -> {auto lte : n `LTE` m} -> Vect m a
rotleftVecNRec3Le n xs0 = rewrite sym (plusZeroRightNeutral m) in go n xs0 [] EmptyV
  where
    go : (n : Nat) -> {0 m : Nat} -> (xs : Vect m a) -> {auto lte : n `LTE` m} -> (ys : Vect k a) -> (acc : SnocVect ys) -> Vect (m + k) a
    go Z xs ys _ = xs ++ ys
    go (S n') {m = S m'} (x::xs') {k = k} ys acc {lte = LTESucc lte'} =
      let prf : S (m' + k) === m' + (k + 1)
          prf = Calc $
                  |~ S (m' + k)
                  ~~ m' + S k
                        ...(plusSuccRightSucc m' k)
                  ~~ m' + S (k + Z)
                        ...(rewrite plusZeroRightNeutral k in Refl)
                  ~~ m' + (k + 1)
                        ...(rewrite plusSuccRightSucc k Z in Refl)
      in rewrite prf in go n' xs' _ (SnocV x ys acc) {lte = lte'}

export
rotleftVecNRec3 : (n : Nat) -> (xs : Vect m a) -> Vect m a
rotleftVecNRec3 n [] = []
rotleftVecNRec3 n {m = S m'} (x::xs') =
  case findRemainder n (length (x::xs')) of
       MkRem _ r {prfR = LTESucc prfR'} =>
         rotleftVecNRec3Le r (x::xs')
                           {lte = rewrite sym (lengthCorrect xs') in lteSuccRight prfR'}


-- Recursive view providing proofs at type level.
data MySnocListRec' : List a -> Type where
  MyNilSnocRec' : MySnocListRec' []
  MySnocRec' : (rest : MySnocListRec' xs) -> (x : a) -> MySnocListRec' (xs ++ [x])

mySnocListRec' : (xs : List a) -> MySnocListRec' xs
mySnocListRec' xs = go xs MyNilSnocRec'
  where
    go : (xs : List a) -> (acc : MySnocListRec' ys) -> MySnocListRec' (ys ++ xs)
    go [] acc = rewrite appendNilRightNeutral ys in acc
    go (x::xs') acc =
      rewrite appendAssociative ys [x] xs' in go xs' (MySnocRec' acc x)

-- xs is erased at runtime, but requires rebuild of a list.
mySnocOutRec' : {0 xs : List a} -> MySnocListRec' xs -> List a
mySnocOutRec' MyNilSnocRec' = []
mySnocOutRec' (MySnocRec' rest x) = mySnocOutRec' rest ++ [x]

-- No rebuild, but xs is not erased.
mySnocOutRec'1 : {xs : List a} -> MySnocListRec' xs -> List a
mySnocOutRec'1 _ = xs

-- These implementations are exactly the same as for 'MySnocListRec', except
-- that here view refines patterns (though i don't need this).
myLastRec' : (xs : List a) -> a
myLastRec' xs with (mySnocListRec' xs)
  myLastRec' [] | MyNilSnocRec' = ?undefLastRec'
  myLastRec' (xs' ++ [x]) | MySnocRec' _ x = x

rotrightRec' : (xs : List a) -> List a
rotrightRec' xs = case (mySnocListRec' xs) of
                   MyNilSnocRec' => []
                   MySnocRec' rest x => x::(mySnocOutRec' rest)

rotleftRec' : (xs : List a) -> List a
rotleftRec' [] = []
rotleftRec' (x::xs') = mySnocOutRec' (MySnocRec' (mySnocListRec' xs') x)

-- So, essentially, SnocList view as described by Wadler, where 'rest' in Snoc
-- view remains as cons-ed list, definitely has sense as demonstrated by
-- examples. View as `MySnocListRec'`, which refines patterns, also has sense,
-- because it refines patterns and may be used for type-level reasoning. But
-- view as 'MySnocListRec' has no sense at all, because it misses cons-ed
-- 'rest' from the Wadler's variant and misses pattern refiniment from the
-- Idris's SnocList.






-- Some leftover from experiments.

decLTE : (x : Nat) -> (y : Nat) -> Dec (LTE x y)
decLTE Z n = Yes LTEZero
decLTE (S t) Z = No uninhabited
decLTE (S t) (S k) = case decLTE t k of
                          Yes lte => Yes (LTESucc lte)
                          No contra => No $ \(LTESucc lte) => contra lte

total
minusLte : (n, m : Nat) -> {auto 0 lte : LTE m n} -> Nat
minusLte n Z {lte = LTEZero} = n
minusLte (S n) (S m) {lte = LTESucc lte} = minusLte n m

-- lteSuccRight, but i need public export to use ltePred in types.
lteSucc : LTE m n -> LTE m (S n)
lteSucc LTEZero = LTEZero
lteSucc {m = S m'} {n = S n'} (LTESucc lte) = LTESucc (lteSucc lte)

-- lteSuccLeft
ltePred : LTE (S m) n -> LTE m n
ltePred LTEZero impossible
ltePred (LTESucc lte) = lteSucc lte

-- FIXME: Can i get rid of it?
ltePred2 : LTE (S m) (S n) -> LTE m n
ltePred2 LTEZero impossible
ltePred2 (LTESucc lte) = lte

total
succMinusSuccNeutral : (n, m : Nat) -> {auto lte : S m `LTE` n} ->
                        S (minusLte n (S m)) = minusLte n m {lte = ltePred lte}
succMinusSuccNeutral Z _ impossible
succMinusSuccNeutral (S n') m' {lte = LTESucc lte} with (lte)
  succMinusSuccNeutral (S n')      Z      | LTEZero = Refl
  succMinusSuccNeutral (S (S n'')) (S m') | LTESucc lte' =
    -- Note here, that though it may seem, that i may just use `lte` here as
    -- lte proof, it won't work as expected and `rec` type will remain
    --
    --      rec : S (minusLte (S n'') (S m')) = minusLte (S n'') m'
    --
    -- i.e. `minusLte (S n'') (S m')` won't be rewritten as `minusLte n'' m'`.
    -- This is because to rewrite `minusLte` by "S"-case, i need `lte` proof
    -- to match with `LTESucc` constructor, but just `lte` may not match.
    -- Therefore, i should explicitly build `LTESucc ..` value as `lte` proof
    -- and then `rec` type will be rewritten correctly to:
    --
    --      rec : S (minusLte n'' m') = minusLte (S n'') m'
    let rec = succMinusSuccNeutral (S n'') m' {lte = LTESucc lte'}
    in rec

data IsLTESucc : LTE n m -> Type where
  ItIsLTESucc : (lte : LTE n m) -> IsLTESucc (LTESucc lte)

total
succMinusIsSucc : (n, t : Nat) -> {auto 0 lte : t `LTE` n} ->
                  minusLte (S n) t {lte = lteSucc lte} = S (minusLte n t)
succMinusIsSucc Z Z = Refl
succMinusIsSucc Z (S t') impossible
succMinusIsSucc (S n') Z = Refl
succMinusIsSucc (S n') (S t') {lte = LTESucc lte} = succMinusIsSucc n' t' {lte = lte}

total
minusLteSuccIsMinusSucc : (n, t : Nat) -> {auto lte : (S t) `LTE` n} ->
         minusLte n t {lte = ltePred lte} `LTE` S u ->
         minusLte n (S t) {lte = lte} `LTE` u
minusLteSuccIsMinusSucc (S n') Z      {lte = LTESucc _} (LTESucc right) = right
-- Or the same using different lemma:
minusLteSuccIsMinusSucc n      (S t') {lte = lte} right =
  let r = succMinusSuccNeutral n (S t') {lte = lte}
  in  ltePred2 (rewrite r in right)
{-
minusLteSuccIsMinusSucc (S n') (S t') {lte = LTESucc lte} right with (lte)
  minusLteSuccIsMinusSucc (S n') (S t') {lte = LTESucc _} right | LTEZero impossible
  minusLteSuccIsMinusSucc (S (S n'')) (S t') {lte = LTESucc _} right | LTESucc lte' =
    let r = succMinusIsSucc n'' t' {lte = lte'}
    in  ltePred2 (rewrite sym r in right)
    -}

lemma : (n : Nat) -> (upper : n `LTE` (S u)) ->
        {t : Nat} -> {auto lte : (S t) `LTE` n} ->
        minusLte n (S t) `LTE` u
lemma (S n') (LTESucc upper) {t = Z} {lte = LTESucc lte} = upper
lemma n      upper {t = S t'} =
  let rec = lemma n upper {t = t'} {lte = ltePred lte}
      res = minusLteSuccIsMinusSucc n (S t') {u = u} {lte = lte} (lteSucc rec)
    in res

total
f : (n : Nat) -> {auto u : Nat} -> {auto upper : n `LTE` u} ->
    (m : Nat) -> {auto lte : m `LTE` n} ->
    Nat
f {u = Z} {upper = LTEZero} Z Z = Z
f {u = S u'} n Z = n
f {u = S u'} n (S t) with (minusLte n (S t) {lte = lte}) proof 0 minusPrf
  _ | Z = Z
  _ | (S k) = case decLTE (S t) (S k) of
                   No _ => S k
                   Yes prf =>
                      let upPrf = lemma n {u = u'} upper {lte = lte}
                          rec = f (S k) (S t) {u = u'} {upper = rewrite sym minusPrf in upPrf}
                      in rec
