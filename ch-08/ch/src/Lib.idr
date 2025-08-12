module Lib

import Data.Vect

{-
reverseV : Vect l a -> Vect l a
reverseV Nil = Nil
reverseV (x :: xs) = go [] (x :: xs)

go : Vect m a -> Vect n a -> Vect (m + n) a
go z Nil = z
go z (x :: xs) = let y = go (x :: z) xs in ?w1
-}

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

zeroPrf : (n : Nat) -> n = 0 + n
zeroPrf n = Refl

zeroPrf2 : (n : Nat) -> n = plus n 0
--zeroPrf2 Z = Refl
--zeroPrf2 (S k) = cong S (zeroPrf2 k)

goRev : {m : Nat} -> Vect m a -> {l : Nat} -> Vect l a -> Vect (plus m l) a
goRev Nil ys = ys
goRev {m = m} xs Nil = ?w4
--  case zeroPrf2 m of
--       Refl => ?w4
goRev (x :: xs) (y :: ys) = ?w3

mySnoc : Vect n a -> a -> Vect (S n) a
mySnoc Nil y = [y]
mySnoc (x :: xs) y = x :: mySnoc xs y

myReverse : {n : Nat} -> Vect n a -> Vect n a
myReverse Nil = Nil
--myReverse (x :: xs) = myReverse xs `mySnoc` x
--myReverse xs@(_ :: _) = goRev [] xs
{-myReverse {n = S k} (x :: xs) =
  let result = myReverse xs ++ [x]
  in rewrite plusCommutative 1 k in result
  -}
myReverse {n = S k} (x :: xs) = reverseProof (myReverse xs ++ [x])
  where
    reverseProof : Vect (plus t 1) a -> Vect (S t) a
    reverseProof {t = t} res = rewrite plusCommutative 1 t in res

test1 : Vect 4 Int
test1 = [1, 2, 3, 4]

test2 : Vect (2 + 2) Int
test2 = test1

zeroRight : {y : Nat} -> y = y + 0
zeroRight {y = Z} = Refl {a = Nat} {x = Z}
--zeroRight {y = S k} = cong S (zeroRight {y = k})
zeroRight {y = S k} = cong S zeroRight

zeroRight' : {y : Nat} -> y + 0 = y
zeroRight' {y = Z} = Refl
zeroRight' {y = S k} = cong S zeroRight'

plusAssoc : (x, y, z : Nat) -> x + (y + z) = (x + y) + z

gg : {k, t : Nat} -> k + (S t) = k + (t + 1)
gg {k = Z} = rewrite plusCommutative t 1 in Refl
gg {k = S p} = cong S gg

ff : {k, t : Nat} -> k + (S t) = t + (S k)
ff = rewrite plusAssociative t 1 k in
     rewrite plusCommutative (t + 1) k in gg

plusComm : {x, y : Nat} -> x + y = y + x
plusComm {x = Z} {y = y} = zeroRight
plusComm {x = S k} {y = Z} = cong S zeroRight'
plusComm {x = S k} {y = S t} = cong S ff
  --rewrite plusAssoc k t 1 in ?x5

