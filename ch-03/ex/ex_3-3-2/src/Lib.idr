module Lib

import Data.Vect

export
total transposeMat : Num a => {n : Nat} -> Vect m (Vect n a) -> Vect n (Vect m a)
transposeMat [] = replicate n []
transposeMat (x :: xs) = zipWith (::) x (transposeMat xs)

export
total addMatrix : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = addVect x y :: addMatrix xs ys
  where
    total addVect : Vect t a -> Vect t a -> Vect t a
    addVect = zipWith (+)

export
total multMatrix : Num a => {m : Nat} -> Vect n (Vect p a) -> Vect p (Vect m a) -> Vect n (Vect m a)
multMatrix xs ys = let ts = transposeMat ys
                   in  map (\x => map (multVect x) ts) xs
  where
    total multVect : Vect t a -> Vect t a -> a
    multVect xs = sum . zipWith (*) xs

main : IO ()
main = putStrLn "Hello from Idris2!"
