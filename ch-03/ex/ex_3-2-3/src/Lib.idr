module Lib

import Data.Vect

export
total myLength : List a -> Nat
myLength [] = Z
myLength (_ :: xs) = S (myLength xs)

export
total myReverse : Vect n a -> Vect n a
myReverse [] = []
--myReverse (x :: xs) = let rs = myReverse xs in snoc rs x
myReverse (x :: xs) = let rs = myReverse xs in mySnoc rs x
  where
    mySnoc : Vect t a -> a -> Vect (S t) a
    mySnoc [] x = [x]
    mySnoc (y :: ys) x = y :: mySnoc ys x

export
total myMap : (a -> b) -> List a -> List b
myMap _ [] = []
myMap f (x :: xs) = f x :: myMap f xs

export
total myMapV : (a -> b) -> Vect n a -> Vect n b
myMapV _ [] = []
myMapV f (x :: xs) = f x :: myMapV f xs

main : IO ()
main = putStrLn "Hello from Idris2!"
