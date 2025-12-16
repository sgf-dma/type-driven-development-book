
import Data.List
import Data.Nat

{-
h : a -> (a, a)
h x = (x, x)

f : (z : a) -> (h : a -> (a, a)) -> (a, a)
-- Работает.
--f z h = let p = h z in (fst p, snd p)
-- И эквивалентная запись тоже работает.
--f z h = (\p => (fst p, snd p)) (h z)

-- Не работает.
f z h = let (x, y) = h z in (x, y)
-- И эквивалентная тоже не работает.
--f z h = case (h z) of
--             (x, y) => (x, y)

-- Работает.
--f z h = (\x => x) (h z)
-- Не компилируется даже эта строчка.
--f z h = (\(MkPair x y) => MkPair x y) (h z)

g : (z : a)  -> snd (f z Main.h) = (snd (h z))
g z = ?a1 -- Refl
-}

{-
data Ty : Type -> Type -> Type where
  MkTy : a -> b -> Ty a b

getTySnd : Ty a b -> b
getTySnd (MkTy x y) = y

h2 : (x, y : a) -> Ty a a
h2 x y = MkTy x y

f2 : (x : a) -> (y : b) -> (a -> b -> Ty a b) -> Ty a b
-- (1) Работает.
--f2 x y h = let z = h x y in z
-- (2) Эквивалентная запись тоже работает.
--f2 x y h = (\z => z) (h x y)

-- (3) Не работает в g2, но работает в g3 .
f2 x y h = let MkTy x' y' = h x y in MkTy x' y'

-- (4) Не компилируется даже эта строчка.
--f2 x y h = (\(MkTy x' y') => MkTy x' y') (h x y)

g2 : (x, y : a)  -> getTySnd (f2 x y Main.h2) = (getTySnd (h2 x y))
g2 x y = ?a2 --Refl

g3 : (x, y : a)  -> getTySnd (f2 x y MkTy) = (getTySnd (MkTy x y))
g3 x y = ?a3 --Refl
-}

f : Int
f = the ((b : _) -> if b then Int else String)
        (\b => case b of True => 1; False => "hello") $ True

divHalf : (n : Nat) -> Nat
divHalf Z = Z
divHalf (S Z) = Z
divHalf (S (S t)) = S (divHalf t)

divHalfEqZero : {n : Nat} -> divHalf n = Z -> n `LTE` (S Z)
divHalfEqZero {n = Z} eq = LTEZero
divHalfEqZero {n = S Z} eq = LTESucc LTEZero
divHalfEqZero {n = S (S k)} eq = absurd eq

data T : List a -> Type where
  MkT : (l : List a) -> (r : List a) -> T (l ++ r)

prf3 : (n : Nat) -> (xs : List a) ->
       --(xs === let (ll, rr) = splitAt n xs in (ll ++ rr))
       (xs === uncurry (++) (splitAt n xs))
prf3 Z xs = Refl
prf3 (S k) [] = Refl
prf3 (S k) (x::xs') with (splitAt k xs') proof 0 eq
  _ | (l, r) =
      let z = prf3 k xs'
        --in ?b3
        in rewrite z in rewrite eq in Refl
        --in replace {p = \y => x::y = x::(l ++ r)} (sym z) ?b3
--prf3 (S k) (x::xs') =
--  let z = prf3 k xs' in rewrite z in ?b3

f3 : (xs : List a) -> (n : Nat) -> T xs
f3 [] _ = MkT [] []
f3 (x::xs') Z = ?a3
f3 (x::xs') (S k) with (splitAt k xs') proof 0 eq
  _ | (l, r) =
        let r = MkT (x::l) r
            p = prf3 k xs'
          in rewrite p in rewrite eq in r


total
splitAtFstLte : (n : Nat) -> (xs : List a) -> length (fst (splitAt n xs)) `LTE` n
splitAtFstLte Z xs = LTEZero
splitAtFstLte (S k) [] = LTEZero
splitAtFstLte (S k) (x::xs') with (splitAt k xs') proof 0 eq
  _ | (tk, dr) = let rec = splitAtFstLte k xs' in
                     rewrite cong fst (sym eq) in
                     LTESucc rec

total
divHalfSuccLteSelf : (n : Nat) -> divHalf (S n) `LTE` n
divHalfSuccLteSelf Z = LTEZero
divHalfSuccLteSelf (S Z) = LTESucc LTEZero
divHalfSuccLteSelf (S (S k)) = let rec = divHalfSuccLteSelf k in LTESucc (lteSuccRight rec)

divHalfLteSelf : (x : Nat) -> divHalf x `LTE` x
divHalfLteSelf Z = LTEZero
divHalfLteSelf (S Z) = LTEZero
divHalfLteSelf (S (S k)) = let rec = divHalfLteSelf k in LTESucc (lteSuccRight rec)

total
f4 : (xs : List Int) -> {m : Nat} -> {auto prf : length xs `LTE` m} -> Int
f4 [] = 0
f4 (x::xs') {m = S k} {prf = LTESucc lte} with (splitAt (divHalf (length (x::xs'))) (x::xs')) proof 0 eq
  _ | (l, r) =
      let
          fstPrf : LTE (length l) (divHalf (S (length xs')))
                 = rewrite cong fst (sym eq) in
                           splitAtFstLte (divHalf (length (x::xs'))) (x::xs')
          recPrf : LTE (length l) k
                 = (fstPrf `transitive` (divHalfSuccLteSelf (length xs')))
                           `transitive` lte
          rec = f4 l {prf = recPrf}
      in rec

total
f4' : (xs : List Int) -> {m : Nat} -> {auto prf : length xs `LTE` m} -> Int
f4' [] = 0
f4' [x] = x
f4' (_::x2::xs') {m = S Z} {prf = LTESucc lte} = absurd lte
f4' (x1::x2::xs') {m = S t@(S k)} {prf = LTESucc (LTESucc lte)} with (splitAt (divHalf (length xs')) (x2::xs')) proof 0 eq
  _ | (l, r) =
      let
          fstPrf : LTE (length l) (divHalf (length xs'))
                 = rewrite cong fst (sym eq) in
                           splitAtFstLte (divHalf (length xs')) (x2::xs')
          recPrf : LTE (length l) k
                 = (fstPrf `transitive` (divHalfLteSelf (length xs')))
                           `transitive` lte
          rec = f4' (x1::l) {m = S k} {prf = LTESucc recPrf}
          --rec = f4' (x1::l) {m = t} {prf = ?b4}
      in ?b3

total
f4'2 : (xs : List Int) -> {m : Nat} -> {auto prf : length xs `LTE` m} -> Int
f4'2 [] = 0
f4'2 [x] = x
f4'2 (x1::x2::xs') {m = S t} {prf = LTESucc lte} with (splitAt (divHalf (length xs')) (x2::xs')) proof 0 eq
  _ | (l, r) with (t)
    f4'2 (x1::x2::xs') {prf = LTESucc lte} | (l, r) | Z = absurd lte
    f4'2 (x1::x2::xs') {prf = LTESucc (LTESucc lte)} | (l, r) | S k =
          let
              fstPrf : LTE (length l) (divHalf (length xs'))
                     = rewrite cong fst (sym eq) in
                               splitAtFstLte (divHalf (length xs')) (x2::xs')
              recPrf : LTE (length l) k
                     = (fstPrf `transitive` (divHalfLteSelf (length xs')))
                               `transitive` lte
              rec = f4'2 (x1::l) {m = S k} {prf = LTESucc recPrf}
          in rec

total
f4'3 : (xs : List Int) -> {m : Nat} -> {auto prf : length xs `LTE` m} -> Int
f4'3 [] = 0
f4'3 [x] = x
f4'3 (x1::x2::xs') {m = S t} {prf = LTESucc lte} with (splitAt (divHalf (length xs')) (x2::xs')) proof 0 eq
  _ | (l, r) with (t)
    _ | Z = absurd lte
    _ | S k =
          let
              fstPrf : LTE (length l) (divHalf (length xs'))
                     = rewrite cong fst (sym eq) in
                               splitAtFstLte (divHalf (length xs')) (x2::xs')
              recPrf : LTE (S (length l)) (S k)
                     = LTESucc (fstPrf `transitive` divHalfLteSelf (length xs'))
                               `transitive` lte
              rec = f4'3 (x1::l) {m = S k} {prf = recPrf}
          in rec

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

splitAtHalfSndLen : (xs : List a) ->
                    length (snd (splitAt (divHalf (length xs)) xs)) `LTE` S (divHalf (length xs))
splitAtHalfSndLen [] = LTEZero
splitAtHalfSndLen [x] = LTESucc LTEZero
splitAtHalfSndLen (_::x::xs') with (splitAt (divHalf (length xs')) (x::xs')) proof 0 eq
  _ | (l, r) =
      let recLte = splitAtHalfSndLen xs'
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

total
divHalfNonZeroSuccLte : (x : Nat) -> S (divHalf (S x)) `LTE` S x
divHalfNonZeroSuccLte Z = LTESucc LTEZero
divHalfNonZeroSuccLte (S k) = let rec = divHalfLteSelf k in LTESucc (LTESucc rec)

total
f5 : (xs : List Int) -> {m : Nat} -> {auto prf : length xs `LTE` m} -> Int
f5 [] = 0
f5 [x] = x
f5 (_::x2::xs') {m = S t} {prf = LTESucc lte} with (splitAt (divHalf (length xs')) (x2::xs')) proof 0 eq
  _ | (l, r) with (t)
    _ | Z = absurd lte
    _ | S k =
        let
            sndPrf : LTE (length r) (S (divHalf (S (length xs'))))
                    = rewrite cong snd (sym eq) in
                              splitConsSndLteSucc x2 (splitHalfSndLteHalfSucc xs')
            prf3 : LTE (S (divHalf (S (length xs')))) (S (length xs'))
                    = LTESucc (divHalfSuccLteSelf (length xs'))
            recPrf : LTE (length r) (S k)
                    = (sndPrf `transitive` prf3) `transitive` lte
            rec = f5 r {m = S k} {prf = recPrf}
        in rec
