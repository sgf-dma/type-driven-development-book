module Main

import Data.Vect

total allLengths : List String -> List Nat
allLengths [] = []
allLengths (x :: xs) = length x :: allLengths xs
--allLengths [] = []
--allLengths (x :: xs) = length x :: allLengths xs

mutual
  isEven : Nat -> Bool
  --isEven Z = True
  --isEven (S n) = not (isEven n)
  isEven Z = True
  isEven (S n) = isOdd n

  isOdd : Nat -> Bool
  isOdd Z = False
  isOdd (S n) = isEven n

--partial allLengthsV : Vect n String -> Vect n Nat
total allLengthsV : Vect n String -> Vect n Nat
--allLengthsV [] = ?a1
allLengthsV [] = []
--allLengthsV (x :: xs) = ?a2
--allLengthsV (x :: xs) = ?a2 :: allLengthsV xs
allLengthsV (x :: xs) = length x :: allLengthsV xs

allLengths' : List String -> List Nat
allLengths' xs = []

--allLengthsV' : Vect n String -> Vect n Nat
--allLengthsV' xs = []

total insert : Ord a => (x : a) -> (xsSorted : Vect k a) -> Vect (S k) a
insert x [] = [x]
insert x (y :: xs) = case x < y of
                          False => y :: insert x xs
                          True => x :: y ::xs

total insSort : Ord a => Vect n a -> Vect n a
insSort [] = []
--insSort (x :: xs) = myInsert x (insSort xs)
insSort (x :: xs) = let xsSorted = insSort xs in insert x xsSorted
  where
    myInsert : a -> Vect t a -> Vect (S t) a
    myInsert x [] = [x]
    myInsert x (y :: ys) = if y < x then y :: insert x ys else x :: y :: ys


partial myReplicate : (n : Nat) -> a -> Vect n a
myReplicate Z _ = []
myReplicate (S n) x = x :: myReplicate n x

total createEmpties : {n : Nat} -> Vect n (Vect 0 a)
createEmpties = myReplicate n []

total createEmpties' : {n : Nat} -> Vect n (Vect 0 a)
createEmpties' {n = Z} = []
--createEmpties' {n = S k} = [] :: createEmpties' {n = k}
--createEmpties' {n = S k} = [] :: ?b
createEmpties' {n = S k} = [] :: createEmpties'

total transposeMat : Num a => {n : Nat} -> Vect m (Vect n a) -> Vect n (Vect m a)
--transposeMat [] = createEmpties {n}
transposeMat [] = createEmpties' {n}
transposeMat (x :: xs) = myZipWith (::) x (transposeMat xs)
  where
    partial myZipWith : (a -> b -> c) -> Vect t a -> Vect t b -> Vect t c
    myZipWith _ [] []  = []
    myZipWith f (x :: xs) (y :: ys) = f x y :: myZipWith f xs ys

append : Vect n a -> Vect m a -> Vect (n + m) a
--append : {a : Type} -> {n : Nat} -> {m : Nat} -> Vect n a -> Vect m a -> Vect (n + m) a
--append [] ys = ys
append [] ys = ?b
append (x :: xs) ys = x :: append xs ys

append' : (a : Type) -> (n : Nat) -> (m : Nat) -> Vect n a -> Vect m a -> Vect (n + m) a
append' _ Z     _ []        ys = ys
append' t (S n) m (x :: xs) ys = x :: append' t n m xs ys

--test : f m a -> b a

lengthV : Vect n a -> Nat
lengthV [] = Z
lengthV (x :: xs) = 1 + lengthV xs

--lengthV' : {n : Nat} -> Vect n a -> (n : Nat)

lengthV'2 : {n : Nat} -> Vect n a -> Nat
--lengthV'2 {n} _ = ?c
lengthV'2 {n} _ = n

main : IO ()
main = putStrLn "Hello from Idris2!"
