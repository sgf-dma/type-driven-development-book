module Lib

import Decidable.Equality
import Data.Vect

%default total

-- I may rewrite resulting type using proof 'prf' and then Refl will prove (y :: xs) = (y :: xs), i.e. just reflexivity.
f : (x = y) -> (xs : Vect n a) -> (x :: xs) = (y :: xs)
f prf xs = rewrite prf in Refl

-- But what about this? Here i can't rewrite resulting type based on existing
-- proof 'prf', because i don't have 'S x' in the result! So, if idris won't
-- infer by itself, that 'S x = S y' means 'x = y', i can't prove succ_inj?
succ_inj : {x, y : Nat} -> S x = S y -> x = y
succ_inj prf@Refl = Refl

add_left_cancel : (x, y, z : Nat) -> (z + x) = (z + y) -> x = y
add_left_cancel _ _ Z prf = rewrite prf in Refl
add_left_cancel x y (S n) prf = add_left_cancel x y n (succ_inj prf)

-- Ex 1.
headEqual : {xs, ys : Vect n a} -> (x :: xs) = (y :: ys) -> x = y
headEqual Refl = Refl

headUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a}
            -> (contra : (x = y) -> Void) -> (x :: xs) = (y :: ys) -> Void
headUnequal contra prf = contra (headEqual prf)

tailEqual : {xs, ys : Vect n a} -> (x :: xs) = (y :: ys) -> xs = ys
tailEqual Refl = Refl

tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a}
            -> (contra : (xs = ys) -> Void) -> (x :: xs) = (y :: ys) -> Void
--tailUnequal contra prf = contra (tailEqual prf)
tailUnequal contra = contra . tailEqual

zero_ne_one : Z = S Z -> Void
zero_ne_one Refl impossible

nat_ne_succ : {n : Nat} -> n = S n -> Void
nat_ne_succ {n = Z} prf = zero_ne_one prf
nat_ne_succ {n = S t} prf = nat_ne_succ (succ_inj prf)

aa : {t : Nat} -> S (S t) = 0

bb : {t : Nat} -> Vect (S (S t)) a
bb {t = t} = rewrite aa {t = t} in ?z1

cc : {t : Nat} -> 0 = S (S t)

dd : Vect 0 a
dd = rewrite cc {t = 1} in ?z2

ee : 0 = S Z
ee = rewrite cc in ?z3

ff : 0 = S p
ff = rewrite cc in ?z4

gg : 0 = S p -> Void
gg = rewrite cc in ?z5

zero_ne_succ : {n : Nat} -> Z = S n -> Void
zero_ne_succ Refl impossible
{-
zero_ne_succ {n = Z} prf = zero_ne_one prf
zero_ne_succ {n = S t} prf =
  let r = zero_ne_succ {n = t}
      --r2 = rewrite prf in rr
  in  ?y2
  where
    rr : 0 = S t -> Void
    rr = rewrite prf in \xx =>
         let r3 = succ_inj xx
             r4 = nat_ne_succ {n = t}
             r5 = sym r3
             r6 = r4 r5
         in  r6
         -}

eqLength : (xs : Vect n a) -> (ys : Vect m a) -> n = m

g : {xs : Vect n a} -> Data.Vect.Nil = (x :: xs) -> Void

zero_vect_ne_nonzero : {xs : Vect n a} -> Data.Vect.Nil = (x :: xs) -> Void
zero_vect_ne_nonzero Refl impossible

eqVectEqLen : {n, m : Nat} -> {xs : Vect n a} -> {ys : Vect m a} -> xs = ys -> n = m
eqVectEqLen Refl = Refl

f2 : DecEq a => {n, m : Nat} -> (xs : Vect n a) -> (ys : Vect m a) -> Dec (xs = ys)
f2 Nil Nil = Yes Refl
f2 Nil (y :: ys') = No zero_vect_ne_nonzero
f2 (x :: xs') Nil = No (\prf => zero_vect_ne_nonzero (sym prf))
f2 {n = S k} (x :: xs') {m = S t} (y :: ys') =
  case f2 xs' ys' of
       Yes Refl => case decEq x y of
                        Yes Refl => Yes Refl
                        No contra => No (\xs_eq_ys => contra (headEqual xs_eq_ys))
       No contra => case decEq k t of
                         Yes Refl => No (contra . tailEqual)
                         --No contra => No (\prf => contra (succ_inj (eqVectEqLen prf)))
                         No contra => No (contra . succ_inj . eqVectEqLen)

f3' : DecEq a => {n : Nat} -> (xs : Vect n a) -> (ys : Vect n a) -> Dec (xs = ys)
f3' Nil Nil = Yes Refl
f3' (x :: xs') (y :: ys') =
  case f3' xs' ys' of
       Yes Refl => case decEq x y of
                        Yes Refl => Yes Refl
                        No contra => No (contra . headEqual)
       No contra => No (contra . tailEqual)

f3 : DecEq a => {n, m : Nat} -> (xs : Vect n a) -> (ys : Vect m a) -> Dec (xs = ys)
f3 {n = n} {m = m} xs ys =
  case decEq n m of
       Yes Refl => f3' xs ys
       --No contra => No (\prf => contra (eqVectEqLen prf))
       No contra => No (contra . eqVectEqLen)

