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
--headUnequal contra Refl = contra Refl
headUnequal contra prf = contra (headEqual prf)

tailEqual : {xs, ys : Vect n a} -> (x :: xs) = (y :: ys) -> xs = ys
tailEqual Refl = Refl

tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a}
            -> (contra : (xs = ys) -> Void) -> (x :: xs) = (y :: ys) -> Void
--tailUnequal contra prf = contra (tailEqual prf)
tailUnequal contra = contra . tailEqual
--tailUnequal contra Refl = contra Refl



zero_ne_one : Z = S Z -> Void
zero_ne_one Refl impossible

nat_ne_succ : {n : Nat} -> n = S n -> Void
nat_ne_succ {n = Z} prf = zero_ne_one prf
nat_ne_succ {n = S t} prf = nat_ne_succ (succ_inj prf)

zero_ne_succ : {n : Nat} -> Z = S n -> Void
zero_ne_succ Refl impossible


-- Ex 2.
zero_vect_ne_nonzero : {xs : Vect n a} -> Data.Vect.Nil = (x :: xs) -> Void
zero_vect_ne_nonzero Refl impossible

eqVectEqLen : {n, m : Nat} -> {xs : Vect n a} -> {ys : Vect m a} -> xs = ys -> n = m
eqVectEqLen Refl = Refl

decEqVectEqLen : DecEq a => {n : Nat} -> (xs : Vect n a) -> (ys : Vect n a) -> Dec (xs = ys)
decEqVectEqLen Nil Nil = Yes Refl
decEqVectEqLen (x :: xs') (y :: ys') =
  case decEqVectEqLen xs' ys' of
       --Yes Refl =>
       Yes xs'_eq_ys' => rewrite xs'_eq_ys'
          in case decEq x y of
                  --Yes Refl => Yes Refl
                  Yes x_eq_y => rewrite x_eq_y in Yes Refl
                  No contra => No (contra . headEqual)
       No contra => No (contra . tailEqual)
       --No contra => No (tailUnequal contra)

-- In fact, 'DecEq' obviously is an interface implemented by a type, thus it's
-- always homogeneous equality. But i've implemented heterogeneous equality by
-- mistake.
decEqVect : DecEq a => {n, m : Nat} -> (xs : Vect n a) -> (ys : Vect m a) -> Dec (xs = ys)
decEqVect {n = n} {m = m} xs ys =
  case decEq n m of
       Yes Refl => decEqVectEqLen xs ys
       --No contra => No (\prf => contra (eqVectEqLen prf))
       No contra => No (contra . eqVectEqLen)

decEqVect2 : DecEq a => {n, m : Nat} -> (xs : Vect n a) -> (ys : Vect m a) -> Dec (xs = ys)
decEqVect2 Nil Nil = Yes Refl
decEqVect2 Nil (y :: ys') = No zero_vect_ne_nonzero
decEqVect2 (x :: xs') Nil = No (\prf => zero_vect_ne_nonzero (sym prf))
decEqVect2 {n = S k} (x :: xs') {m = S t} (y :: ys') =
  case decEqVect2 xs' ys' of
       Yes Refl => case decEq x y of
                        Yes Refl => Yes Refl
                        No contra => No (\xs_eq_ys => contra (headEqual xs_eq_ys))
                        --No contra => No (headUnequal contra)
       No contra => case decEq k t of
                         --Yes Refl => No (contra . tailEqual)
                         Yes Refl => No (tailUnequal contra)
                         --No contra => No (\prf => contra (succ_inj (eqVectEqLen prf)))
                         No contra => No (contra . succ_inj . eqVectEqLen)
