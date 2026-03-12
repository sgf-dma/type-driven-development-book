module Lib

import Syntax.PreorderReasoning
import Data.Nat
import Data.Fin

%default total

-- Ex 1.
data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> {rest : List a} -> TakeN (n_xs ++ rest)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S t) [] = Fewer
takeN (S t) (x::xs') = case takeN t xs' of
                            Fewer => Fewer
                            Exact n_xs => Exact (x::n_xs)

partial
groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | Exact n_xs = n_xs :: groupByN n rest

-- Ex 2.

halves : List a -> (List a, List a)
halves xs with (takeN (length xs `div` 2) xs)
  halves xs | Fewer = ?impossible1
  halves (n_xs ++ rest) | Exact n_xs = (n_xs, rest)

-- Try to prove, that 'Fewer' case above is impossible.
data Half : Nat -> Type where
  MkHalf : (a : Nat) -> {d : Fin 2} ->
                        {auto halfSum : b = finToNat d + 2*a} ->
                        Half b

halfToNat : Half b -> Nat
halfToNat (MkHalf a) = a

half : (x : Nat) -> Half x
half Z = MkHalf Z {d = FZ}
half (S k) = case half k of
                  MkHalf a {d = FZ} {halfSum = halfSum} =>
                                let t = MkHalf a {d = FS FZ}
                                in rewrite halfSum in t
                  MkHalf a {d = FS FZ} {halfSum = halfSum} =>
                                let t = MkHalf (S a) {d = FZ}
                                in rewrite halfSum
                                in rewrite plusSuccRightSucc a (plus a 0)
                                in t
                  MkHalf a {d = FS (FS _)} impossible

-- But in fact, `Half` is useless, because by pattern matching on `TakeN`
-- i can't derive anything about list length. Or, in other words, because
-- 'TakeN' does not provides any hints about requested and resulted list
-- length.
halves' : List a -> (List a, List a)
halves' xs with (takeN (halfToNat (half (length xs))) xs)
  halves' xs | Fewer = ?impossible2
  halves' (n_xs ++ rest) | Exact n_xs = (n_xs, rest)

-- Thus, i need a different 'TakeN' definition.
data TakeN2 : Nat -> List a -> Type where
  Fewer2 : {xs : List a} -> {k : Nat} -> TakeN2 (S k + length xs) xs
  Exact2 : (n_xs : List a) -> {rest : List a} -> TakeN2 (length n_xs) (n_xs ++ rest)

takeToList : {xs : List a} -> TakeN2 n xs -> List a
takeToList (Fewer2 {xs = xs}) = xs
takeToList (Exact2 n_xs) = n_xs

takeN2 : (n : Nat) -> (xs : List a) -> TakeN2 n xs
takeN2 Z xs = Exact2 []
takeN2 (S t) [] = rewrite sym (plusZeroRightNeutral t) in Fewer2
takeN2 (S t) (x::xs') = case takeN2 t xs' of
                             Fewer2 {k = k} =>
                                rewrite plusSuccRightSucc k (length xs') in
                                        Fewer2
                             Exact2 n_xs => Exact2 (x::n_xs)

zero_ne_succ : {n : Nat} -> 0 = S n -> Void
zero_ne_succ Refl impossible

ne_plus_succ : {t, n : Nat} -> n = plus n (S t) -> Void
ne_plus_succ eq = let r1 : n + 0 === n + (S t)
                             = rewrite plusZeroRightNeutral n in eq
                        --in zero_ne_succ (plusLeftCancel n 0 (S t) r1)
                        in uninhabited (plusLeftCancel n 0 (S t) r1)

-- Added later: here, though function splits input list into two halves, i
-- don't have proofs, that resulting list are indeed halves. See exercises
-- 10.2 for implementation of view `Half`, which provides these proofs.
halves2 : (xs : List a) -> {t : Nat} ->
                     {auto d : Fin 2} ->
                     {auto halfSum : length xs = 2*t + finToNat d} ->
                     (List a, List a)
halves2 xs {halfSum = halfSum} with (takeN2 t xs)
  halves2 xs {halfSum = halfSum} | Fewer2 {k = k} =
    let h : {n, w, q : Nat} -> n === S (plus (plus (plus k n) w) q) -> Void
        h eq =
          let r : n === plus n (S (plus (plus k w) q))
                = do
                    rewrite sym (plusSuccRightSucc n (plus (plus k w) q))
                    rewrite plusAssociative n (plus k w) q
                    rewrite plusAssociative n k w
                    rewrite plusCommutative n k
                    eq
          in ne_plus_succ r
    in  void (h halfSum)
  halves2 (n_xs ++ rest) | Exact2 n_xs = (n_xs, rest)

