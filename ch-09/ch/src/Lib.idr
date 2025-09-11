module Lib

import Decidable.Equality
import Data.Vect
import Data.Vect.Elem

removeElem' : DecEq a => (value : a) -> {n : Nat} -> (xs : Vect n a) -> (m ** Vect m a)
removeElem' _ Nil = (0 ** Nil)
removeElem' value {n = S t} (x :: xs) =
  case decEq x value of
       Yes _ => (t ** xs)
       No contra => let (m ** xs') = removeElem' value xs
                    in (S m ** x :: xs')

maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)

succ_pred_eq_id : {n : Nat} -> S (pred n) = n
succ_pred_eq_id {n = Z} = ?w1
succ_pred_eq_id {n = S t} = Refl

removeElem2 : (value : a) -> {n : Nat}
            -> (xs : Vect n a)
            -> (prf : Elem value xs) -> Vect (pred n) a
removeElem2 value (value :: xs) Here = xs
removeElem2 value {n = S t} (x :: xs) (There later) =
  let res = x :: removeElem2 value xs later
  in  rewrite sym (succ_pred_eq_id {n = t}) in res

data MyElem : (value : a) -> (xs : Vect k a) -> Type where
  MyHere : {x : a} -> {xs : Vect k a} -> MyElem x (x :: xs)
  MyThere : {xs : Vect (S n) a} -> (later : MyElem x xs) -> MyElem x (y :: xs)

removeElem3My : (value : a)
              -> (xs : Vect n a)
              -> (prf : MyElem value xs) -> Vect (pred n) a
removeElem3My value (value :: xs) MyHere = xs
removeElem3My value (x :: xs) (MyThere later) =
  let res = removeElem3My value xs later
  in x :: res

removeElem3My' : (value : a)
               -> (xs : Vect (S n) a)
               -> (prf : MyElem value xs) -> Vect n a
removeElem3My' value (value :: xs) MyHere = xs
removeElem3My' value (x :: xs) (MyThere later) =
  let res = removeElem3My' value xs later
  in x :: res

removeElem3 : (value : a)
            -> (xs : Vect (S n) a)
            -> (prf : Elem value xs) -> Vect n a
removeElem3 value (value :: xs) Here = xs
removeElem3 value (x :: xs) (There later) =
  case later of
       Here => let res = removeElem3 value xs Here in x :: res
       There later2 => let res = removeElem3 value xs (There later2) in x :: res

removeElem : (value : a) -> {n : Nat}
            -> (xs : Vect (S n) a)
            -> (prf : Elem value xs) -> Vect n a
removeElem value (value :: xs) Here = xs
removeElem {n = Z} value (x :: []) (There later) = absurd later
removeElem {n = S t} value (x :: xs) (There later) =
  let res = removeElem value xs later
  in x :: res

twoplustwo_not_five : 2 + 2 = 5 -> Void
twoplustwo_not_five Refl impossible

Uninhabited (2 + 2 = 5) where
  uninhabited Refl impossible

emptyElem : Elem x [] -> Void
emptyElem prf impossible

removeElem_auto : (value : a) -> {n : Nat}
            -> (xs : Vect (S n) a)
            -> {auto prf : Elem value xs} -> Vect n a
removeElem_auto value xs {prf = prf} = removeElem value xs prf

notInTail : Not (value = x) -> Not (Elem value xs) -> Not (Elem value (x :: xs))
notInTail notHere _ Here = notHere Refl
notInTail _ notThere (There later) = notThere later

isElem2 : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem value xs)
isElem2 value [] = No uninhabited
isElem2 value (x :: xs) =
  case decEq value x of
       Yes prf => rewrite prf in Yes Here
       No notHere => case isElem2 value xs of
                     Yes prf => Yes (There prf)
                     No notThere => No (notInTail notHere notThere)

