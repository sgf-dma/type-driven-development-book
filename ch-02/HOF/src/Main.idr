module Main

double : Num ty => ty -> ty
double x = x + x

quadruple : Num a => a -> a
quadruple x = double (double x)

Shape : Type

rotate : Shape -> Shape

turn_around : Shape -> Shape
turn_around x = rotate (rotate x)

twice : (a -> a) -> a -> a
twice f x = f (f x)

quadruple2 : Num a => a -> a
quadruple2 = twice double

turn_around2 : Shape -> Shape
turn_around2 = twice rotate

longer : String -> String -> Nat
longer word1 word2 = let len1 = length in if (len1 word1) > len2 then len1 word1 else len2
  where
    len2 = length word2

main : IO ()
main = putStrLn "Hello from Idris2!"
