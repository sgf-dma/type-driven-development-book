module Lib

import Decidable.Equality
import Data.Vect

myExactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
myExactLength Z Nil = Just Nil
myExactLength Z _ = Nothing
myExactLength (S n) Nil = Nothing
myExactLength (S n) (x :: xs) = (x ::) <$> myExactLength n xs

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

sameS : (k : Nat) -> (j : Nat) -> EqNat k j -> EqNat (S k) (S j)
sameS t t (Same t) = Same (S t)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (Same Z)
checkEqNat (S k) (S j) = case checkEqNat k j of
                                Nothing => Nothing
                                --Just (Same n) => Just (Same (S n))
                                Just eq => Just (sameS _ _ eq)
checkEqNat _ _ = Nothing

--myExactLength2 : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
myExactLength2 : (len : Nat) -> {m : Nat} -> (input : Vect m a) -> Maybe (Vect len a)
myExactLength2 len {m} input = case checkEqNat len m of
                                Nothing => Nothing
                                Just (Same l) => Just input

checkEqNat2 : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat2 Z Z = Just Refl
checkEqNat2 (S k) (S j) = case checkEqNat2 k j of
                                Nothing => Nothing
                                --Just Refl => Just Refl
                                Just prf => Just (cong S prf)
checkEqNat2 _ _ = Nothing

myCong : {t : Type} -> {u : Type} -> {a : t} -> {b : t} -> (f : t -> u) -> (_ : a = b) -> f a = f b
--myCong {a = a} f Refl = Refl {a = u} {x = f a}
myCong {a = a} f Refl = Refl

mySnoc : Vect n a -> a -> Vect (S n) a
mySnoc Nil y = [y]
mySnoc (x :: xs) y = x :: mySnoc xs y

myReverse : {n : Nat} -> Vect n a -> Vect n a
myReverse Nil = Nil
--myReverse (x :: xs) = myReverse xs `mySnoc` x
myReverse {n = S k} (x :: xs) = reverseProof (myReverse xs ++ [x])
  where
    reverseProof : Vect (plus t 1) a -> Vect (S t) a
    reverseProof {t = t} res = rewrite plusCommutative 1 t in res

test1 : Vect 4 Int
test1 = [1, 2, 3, 4]

test2 : Vect (2 + 2) Int
test2 = test1

addZero : {y : Nat} -> y + 0 = y
addZero {y = Z} = Refl {a = Nat} {x = Z}
--addZero {y = S k} = cong S (addZero {y = k})
addZero {y = S k} = cong S addZero

symm : a = b -> b = a
symm Refl = Refl

-- By induction.
addSucc : {x, y: Nat} -> plus x (S y) = S (plus x y)
addSucc {x = Z} = Refl
--addSucc {x = S k} = cong S (addSucc {x = k})
addSucc {x = S k} = cong S addSucc

-- By induction over both args.
plusComm : {x, y : Nat} -> x + y = y + x
plusComm {x = Z} {y = y} = symm addZero
plusComm {x = S k} {y = Z} = cong S addZero
plusComm {x = S k} {y = S t} =
  rewrite (addSucc {x = k} {y = t}) in
  rewrite (addSucc {x = t} {y = k}) in
  rewrite (cong S (plusComm {x = k} {y = t}))
  in cong S Refl

-- In fact, this does not needed, because this follows from 'plus' definition.
succAdd : {x, y : Nat} -> plus (S x) y = S (plus x y)
succAdd {x = Z} = Refl
succAdd {x = S k} = cong S (succAdd {x = k})
--succAdd {x = S k} = cong S succAdd

-- Proper proof, by induction over one argument only.
plusComm' : {x, y : Nat} -> x + y = y + x
plusComm' {x = Z} = symm addZero
plusComm' {x = S k} {y = y} =
  rewrite (addSucc {x = y} {y = k}) in
  rewrite (plusComm' {x = k} {y = y})
  in Refl

plusAssoc : {x, y, z : Nat} -> x + (y + z) = (x + y) + z
plusAssoc {x = Z} = Refl
plusAssoc {x = S k} = cong S plusAssoc

myAppend : Vect n a -> Vect m a -> Vect (n + m) a
myAppend Nil ys = ys
myAppend (x :: xs) ys = x :: myAppend xs ys

myAppend' : Vect n a -> Vect m a -> Vect (n + m) a
myAppend' {n = n} xs Nil = rewrite addZero {y = n} in xs
myAppend' {n = n} xs {m = S k} (y :: ys) =
  rewrite addSucc {x = n} {y = k}
  in myAppend' (xs `snoc` y) ys

myAppend'2 : Vect n a -> Vect m a -> Vect (m + n) a
myAppend'2 xs Nil = xs
myAppend'2 {n = n} xs {m = S k} (y :: ys) =
  rewrite symm (addSucc {x = k} {y = n})
  in myAppend'2 (xs `snoc` y) ys

myAppend'3 : Vect n a -> Vect m a -> Vect (m + n) a
--myAppend'3 Nil {m = m} xs = rewrite addZero {y = m} in xs
myAppend'3 Nil {m = m} xs = rewrite plusZeroRightNeutral m in xs
myAppend'3 {n = S k} (x :: xs) {m = m} ys =
  let z = x :: myAppend'3 xs ys
  --in  rewrite addSucc {x = m} {y = k}
  in  rewrite sym (plusSuccRightSucc m k)
  in  z

succ_inj : S x = S y -> x = y
succ_inj Refl = Refl

zero_ne_succ : {x : Nat} -> 0 = S x -> Void
zero_ne_succ Refl impossible

twoPlusTwoNotFive : 2 + 2 = (the Nat 5) -> Void
twoPlusTwoNotFive Refl impossible
{-
  let r = succ_inj (succ_inj (succ_inj (succ_inj h)))
  in  zero_ne_succ r
  -}

checkEqNat3 : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat3 Z Z = Yes Refl
checkEqNat3 Z (S t) = No zero_ne_succ
--checkEqNat3 (S n) Z = No (symmV zero_ne_succ)
checkEqNat3 (S n) Z = No (zero_ne_succ . symm)
  where
    symmV : (a = b -> Void) -> b = a -> Void
    --symmV h prf = h (symm prf)
    symmV h = h . symm
checkEqNat3 (S n) (S t) =
  case checkEqNat3 n t of
       --Yes Refl => Yes Refl
       Yes prf => rewrite prf in Yes Refl
       No contra => No (succ_ne_succ' contra)
  where
    succ_ne_succ' : (n = t -> Void) -> S n = S t -> Void
    succ_ne_succ' h prf = h (succ_inj prf)

succ_ne_succ : (n = t -> Void) -> S n = S t -> Void
succ_ne_succ contra Refl = contra Refl

myExactLength3 : (len : Nat) -> {m : Nat} -> Vect m a -> Maybe (Vect len a)
myExactLength3 len {m = m} xs = case decEq len m of
                                     Yes prf => rewrite prf in Just xs
                                     --Yes Refl => Just xs
                                     No contra => Nothing
