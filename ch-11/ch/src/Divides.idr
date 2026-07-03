-- This is essentially a copy of ../../ch-10/wadler-views/src/Remainder.idr
-- with some modifications to make definitions match with 'Data.Primitives.Views.Divides' .

module Divides

import Data.Nat
import Syntax.PreorderReasoning

data SumView : Nat -> Nat -> Type where
  MkSumView : (q : Nat) -> SumView (m + q) m
  NoSumView : {auto nLTm : n `LT` m} -> SumView n m

sumView2 : (n, m : Nat) -> SumView n m
sumView2 Z Z = MkSumView 0
sumView2 Z (S m') = NoSumView
sumView2 (S n') Z = MkSumView (S n')
sumView2 (S n') (S m') =
  case sumView2 n' m' of
       MkSumView q => MkSumView q
       NoSumView {nLTm} => NoSumView

public export
data Divides : Nat -> Nat -> Type where
  DivByZero : Divides x 0
  DivBy : {auto 0 isS : IsSucc d} ->
          (div, rem : Nat) -> {auto prfR : rem `LT` d} ->
          Divides (d*div + r) d

plusRightLte : {n : Nat} -> {0 m : Nat} -> (n + m) `LTE` k -> m `LTE` k
plusRightLte {n = Z} lte = lte
plusRightLte {n = S n} (LTESucc lte) = let rec = plusRightLte {n = n} lte in lteSuccRight rec

divides' : (val : Nat) -> {auto upper : val `LTE` u} ->
           (d : Nat) -> {auto 0 isS : IsSucc d} ->
           (kAcc : Nat) -> Divides (d*kAcc + val) d
divides' val (S d') kAcc {upper} with (sumView2 val (S d'))
  _ | NoSumView {nLTm} = DivBy kAcc val
  divides' (S (d' + q)) (S d') kAcc {upper = LTESucc up} | MkSumView q =
    let rec = divides' q (S d') (S kAcc) {upper = plusRightLte {n = d'} up}
        eqPrf : (kAcc + d' * kAcc) +  S (d' + q) === S ((kAcc + d' * S kAcc) + q)
        eqPrf = Calc $
                  |~ (kAcc + d'*kAcc) +  S (d' + q)
                  ~~ S ((kAcc + d'*kAcc) +  (d' + q))
                      ...(sym (plusSuccRightSucc (kAcc + d' * kAcc) (d' + q)))
                  ~~ S (((kAcc + d'*kAcc) +  d') + q)
                      ...(rewrite plusAssociative (kAcc + d' * kAcc) d' q in Refl)
                  ~~ S ((kAcc + (d'*kAcc +  d')) + q)
                      ...(rewrite plusAssociative kAcc (d' * kAcc) d' in Refl)
                  ~~ S ((kAcc + (d' + d'*kAcc)) + q)
                      ...(rewrite plusCommutative d' (d'*kAcc) in Refl)
                  ~~ S ((kAcc + (d' * S kAcc)) + q)
                      ...(rewrite multRightSuccPlus d' kAcc in Refl)
    in rewrite eqPrf in rec

lteSelf : {n : Nat} -> LTE n n
lteSelf {n = Z} = LTEZero
lteSelf {n = S n'} = LTESucc lteSelf

export
divides : (val : Nat) -> (d : Nat) -> Divides val d
divides n Z = DivByZero
divides n (S m') =
  let rec = divides' n {upper = lteSelf} (S m') 0
      prf : n === m'*0 + n
      prf = Calc $
              |~ n
              ~~ 0 + n ...(Refl)
              ~~ m'*0 + n ...(rewrite multZeroRightZero m' in Refl)
  in rewrite prf in rec

