module Lib

import Data.Nat
import Data.List
import Data.List.Views
import Decidable.Equality
import Syntax.PreorderReasoning

%default total
-- 2 Viewing an integer as zero or a succesor

data ViewType = Zero | Succ Int

viewin : Int -> ViewType
viewin n = if n == 0 then Zero
              else if n > 0 then Succ (n - 1)
              else ?undef1

viewout : ViewType -> Int
viewout Zero = 0
viewout (Succ n) = n + 1

partial
fib : (m : Int) -> Int
fib m =
  case viewin m of
       Zero => viewout Zero
       (Succ m) => case viewin m of
                        Zero => viewout (Succ (viewout Zero))
                        (Succ n) => fib n + fib (viewout (Succ n))


-- 5.Viewing a list backwards

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
rotrightN (S t) xs = case (mySnocList xs) of
                       MyNilSnoc => []
                       MySnoc rest x => rotrightN t (x::rest)

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

-- Recursive view.
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
-- second from last element.
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
export
partial
rotrightNRec : (n : Nat) -> (xs : List a) -> List a
rotrightNRec n xs = go n [] (mySnocListRec xs)
  where
    go : (n : Nat) -> (acc : List a) -> (rest : MySnocListRec a) -> List a
    go Z acc rest = acc ++ (mySnocOutRec rest)
    -- Wrong, but pass totality checker.
    --go (S t) acc MyNilSnocRec = []
    -- Following case breaks totality check. And i don't know a fix for it,
    -- except rewrite to more restricted version below.
    go (S t) acc MyNilSnocRec = go (S t) [] (mySnocListRec acc)
    go (S t) acc (MySnocRec rest x) = go t (x::acc) rest




-- Not used
cmpSucc : CmpNat x y -> CmpNat (S x) (S y)
cmpSucc (CmpLT t) = CmpLT t
cmpSucc CmpEQ = CmpEQ
cmpSucc (CmpGT t) = CmpGT t

cmp : (x : Nat) -> (y : Nat) -> CmpNat x y
cmp Z Z = CmpEQ
cmp Z (S t) = CmpLT t
cmp (S k) Z = CmpGT k
cmp (S k) (S t) = let rec = Lib.cmp k t in cmpSucc rec

decLTE : (x : Nat) -> (y : Nat) -> Dec (LTE x y)
decLTE Z n = Yes LTEZero
decLTE (S t) Z = No uninhabited
decLTE (S t) (S k) = case decLTE t k of
                          Yes lte => Yes (LTESucc lte)
                          No contra => No $ \(LTESucc lte) => contra lte



go : (n : Nat) -> (acc : List a) -> (rest : MySnocListRec a) ->
     {prf : LTE n (length (mySnocOutRec rest))} -> List a

-- Optimized version, which shortcircuits rotations by more, than (length xs).
rotrightNRec' : (n : Nat) -> (xs : List a) -> {l : Nat} -> {auto 0 _ : l = length xs} -> List a
rotrightNRec' n xs with (Lib.cmp n l) proof 0 comp
  rotrightNRec' n xs | CmpLT t = ?a1
  rotrightNRec' n xs | CmpEQ = ?a2
  rotrightNRec' (m + S t) xs | CmpGT t = ?a3

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

fff : (l : LTE n m) -> IsLTESucc l -> Int
fff (LTESucc lte) (ItIsLTESucc _) = ?ww1

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

data Remainder : Nat -> Nat -> Type where
  MkRem : {n, m : Nat} -> {auto lte : m `LTE` n} -> (k, r : Nat) -> {auto 0 prf1 : n = k*m + r} -> {auto 0 prf2 : r `LTE` m} -> Remainder n m

multOneRight : (n : Nat) -> n `mult` 1 = n

minusEqZero : (n, m : Nat) -> {auto lte : m `LTE` n} -> minusLte n m = 0 -> n = m

minusEqPlus : (n, m, k : Nat) -> {auto lte : m `LTE` n} -> minusLte n m = k -> n = m + k

plusLteRight : (n + m) `LTE` k -> m `LTE` k

multDistOverPlusLeft : (a, b, c : Nat) -> (a + b) * c = a * c + b * c

multDistOverPlusRight : (a, b, c : Nat) -> a * (b + c) = a * b + a * c

multSuccLeft : (a, b : Nat) -> (a + 1) * b = b + a * b

-- FIXME: Rewrite using Calc.
total
f2 : (n : Nat) -> {auto u : Nat} -> {auto upper : n `LTE` u} ->
     (m : Nat) -> {auto lte : S m `LTE` n} -> Remainder n (S m)
f2 {upper = LTEZero} Z Z impossible
f2 n Z = MkRem n 0 {prf1 = rewrite multOneRight n in
                           rewrite plusZeroRightNeutral n in
                                   Refl}
f2 n {u = S u'} m with (minusLte n (S m)) proof 0 minusPrf
  _ | Z = MkRem 1 0 {prf1 =  rewrite plusZeroRightNeutral m in
                             rewrite plusZeroRightNeutral m in
                                     minusEqZero n (S m) minusPrf}
  _ | (S t) with (decEq (S m) (S t))
    _ | Yes prf = MkRem 2 0 {prf1 = rewrite plusZeroRightNeutral m in
                                    rewrite plusZeroRightNeutral (plus m (S m)) in
                                    rewrite prf in
                                    minusEqPlus n (S m) (S t) minusPrf}
    _ | No contra with (connex contra {rel = LTE})
      _ | Left smLteSk =
              -- Either use the same proof as in f, or..
              let upPrf : S (m + (S t)) `LTE` S u'
                  upPrf = rewrite sym (minusEqPlus n (S m) (S t) minusPrf) in upper
                  rec = f2 (S t) {u = u'} m {upper = plusLteRight (ltePred2 upPrf)} {lte = smLteSk}
              in case rec of
                  MkRem k r {prf1 = prf1} {prf2 = prf2} =>
                    MkRem (k+1) r {prf2 = prf2}
                                  {prf1 = rewrite multDistOverPlusLeft k 1 (S m) in
                                          rewrite plusZeroRightNeutral m in
                                          rewrite minusEqPlus n (S m) (S t) minusPrf in
                                          rewrite prf1 in
                                          rewrite sym (plusSuccRightSucc (mult k (S m)) m) in
                                          rewrite plusCommutative (mult k (S m)) m in
                                          rewrite sym (plusAssociative m (mult k (S m)) r) in
                                                  Refl}
      _ | Right skLteSm =
              MkRem 1 (S t) {prf2 = skLteSm}
                            {prf1 = rewrite plusZeroRightNeutral m in
                                    minusEqPlus n (S m) (S t) minusPrf}

total
f3 : (n : Nat) -> {auto u : Nat} -> {auto upper : n `LTE` u} ->
     (m : Nat) -> {auto lte : S m `LTE` n} -> Remainder n (S m)
f3 {upper = LTEZero} Z Z impossible
f3 n Z = MkRem n 0 {prf1 = Calc $ |~ n
                                  ~~ n * 1 ...(sym (multOneRight n))
                                  ~~ (n * 1) + 0 ...(sym (plusZeroRightNeutral (n * 1))) }
f3 n {u = S u'} m with (minusLte n (S m)) proof 0 minusPrf
  _ | Z = MkRem 1 0 {prf1 = Calc $
                              |~ n
                              ~~ S m ...(minusEqZero n (S m) minusPrf)
                              ~~ S (m + 0) ...(sym (plusZeroRightNeutral (S m)))
                              ~~ S ((m + 0) + 0) ...(sym (plusZeroRightNeutral (S (m + 0)))) }
  _ | (S t) with (decEq (S m) (S t))
    _ | Yes prf = MkRem 2 0 {prf1 = Calc $
                              |~ n
                              ~~ S m + S t ...(minusEqPlus n (S m) (S t) minusPrf)
                              ~~ S m + S m ...(rewrite prf in Refl)
                              ~~ S m + (S m + 0) ...(rewrite plusZeroRightNeutral (S m) in Refl)
                              -- ~~ S m + (S m + 0) ...(rewrite plusZeroRightNeutral (S m) in
                              --                        rewrite prf in
                              --                                minusEqPlus n (S m) (S t) minusPrf)
                              ~~ S (m + (S m + 0)) + 0 ...(sym (plusZeroRightNeutral (S m + (S m + 0)))) }
                              -- ~~ S (m + (S m + 0)) + 0 ...(Refl) }
                            {-rewrite plusZeroRightNeutral m in
                                    rewrite plusZeroRightNeutral (plus m (S m)) in
                                    rewrite prf in
                                            minusEqPlus n (S m) (S t) minusPrf-}
    _ | No contra with (connex contra {rel = LTE})
      _ | Left smLteSk =
              -- Either use the same proof as in f, or..
              let upPrf : S (m + (S t)) `LTE` S u'
                  upPrf = rewrite sym (minusEqPlus n (S m) (S t) minusPrf) in upper
                  rec = f3 (S t) {u = u'} m {upper = plusLteRight (ltePred2 upPrf)} {lte = smLteSk}
              in case rec of
                  MkRem k r {prf1 = prf1} {prf2 = prf2} =>
                    MkRem (k+1) r {prf2 = prf2}
                                  {prf1 = Calc $
                                      |~ n
                                      ~~ S (m + S t)
                                           ...(minusEqPlus n (S m) (S t) minusPrf)
                                      ~~ S (m + (k * S m + r))
                                           ...(rewrite sym prf1 in Refl)
                                      ~~ m + (S (k * S m + r))
                                           ...(plusSuccRightSucc m (k * S m + r))
                                      ~~ (m + 1) + (k * S m + r)
                                           ...(plusAssociative m 1 (k * S m + r))
                                      ~~ (m + 1) + (k * (m + 1) + r)
                                           ...(rewrite plusCommutative 1 m in Refl)
                                      ~~ ((m + 1) + k * (m + 1)) + r
                                           ...(plusAssociative (m + 1) (k * (m + 1)) r)
                                      ~~ ((k + 1) * (m + 1)) + r
                                           ...(rewrite sym (multSuccLeft k (m + 1)) in Refl)
                                      ~~ ((k + 1) * (S (m + 0))) + r
                                           ...(rewrite sym (plusSuccRightSucc m 0) in Refl)
                                      ~~ ((k + 1) * (S m)) + r
                                           ...(rewrite plusZeroRightNeutral m in Refl) }
                                          {-rewrite multDistOverPlusLeft k 1 (S m) in
                                          rewrite plusZeroRightNeutral m in
                                          rewrite minusEqPlus n (S m) (S t) minusPrf in
                                          rewrite prf1 in
                                          rewrite sym (plusSuccRightSucc (mult k (S m)) m) in
                                          rewrite plusCommutative (mult k (S m)) m in
                                          rewrite sym (plusAssociative m (mult k (S m)) r) in
                                                  Refl
                                                  -}
      _ | Right skLteSm =
              MkRem 1 (S t) {prf2 = skLteSm}
                            {prf1 = Calc $
                                      |~ n
                                      ~~ S m + S t ...(minusEqPlus n (S m) (S t) minusPrf)
                                      ~~ S ((m + 0) + S t) ...(rewrite sym (plusZeroRightNeutral m) in Refl)
                            }
                            {-rewrite plusZeroRightNeutral m in
                                    minusEqPlus n (S m) (S t) minusPrf}








example : (x : Nat) -> (x + 1) + 0 = 1 + x
example x =
  Calc $
   (?d1 {-|~ (x + 1) + 0
   ~~ x+1  ...( plusZeroRightNeutral $ x + 1 ) -}
   ~~ 1+x  ...( plusCommutative x 1          ))


lemmaNR : (n, t : Nat) -> (upper : n `LTE` u) ->
          {auto 0 lte : t `LTE` n} -> minusLte n t `LTE` u
lemmaNR n      Z      upper {lte = LTEZero} = upper
lemmaNR Z      (S t') _ impossible
lemmaNR (S n') (S t') upper {lte = LTESucc lte} =
  lemmaNR n' t' (ltePred upper) {lte = lte}

-- FIXME: Can i generalize following function into "find minus operation
-- remainder with a proof, that it's indeed a remainder"?
total
-- FIXME: `l` is not used.
-- FIXME: So, what will happen, if `u` is not bound in any way to `n`?
rotrightNRec'2 : (n : Nat) -> {u : Nat} -> {auto upper : n `LTE` u} ->
                 (xs : List a) -> {l : Nat} -> {auto 0 _ : l = length xs} -> List a
rotrightNRec'2 Z xs = xs
rotrightNRec'2 (S n') {u = S u'} {upper = LTESucc upper} [] = []
rotrightNRec'2 (S n') {u = S u'} {upper = LTESucc upper} (x::xs') with (decEq (S n') (length (x::xs')))
  _ | Yes _ = x::xs'
  _ | No contra with (connex {rel = LTE} contra)
    _ | Left lte = ?b3
    _ | Right (LTESucc gt) with (minusLte (S n') (length (x::xs')) {lte = LTESucc gt}) proof 0 minusPrf
      _ | r =
        let upPrf = lemmaNR n' {u = u'} (length xs') upper {lte = gt}
            rec = rotrightNRec'2 r (x::xs') {u = u'} {upper = rewrite sym minusPrf in ?b2}
          in rec


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

rotleftNRec : (n : Nat) -> (xs : List a) -> List a
--rotleftNRec Z xs = xs
--rotleftNRec (S t) (x::xs') =

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
