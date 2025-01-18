module Main

import Data.String
import System.REPL

rev : List a -> List a
--rev xs0 = foldr (\x => \z => \ys => z (x :: ys)) id xs0 []
rev xs0 = foldr (\x => \z => z . (x ::)) id xs0 []

||| Ex 2, 3, 4, 5.
palindrome : Nat -> String -> Bool
palindrome n str = if length str > n
                    then let xs = unpack (toLower str) in  xs == rev xs
                    else False
--palindrome str = str == reverse str

||| Ex 6.
counts : String -> (Nat, Nat)
--counts str = let ws = words str in (length ws, sum (map length ws))
counts str = (length (words str), length str)

take' : Nat -> List a -> List a
take' n xs0 = foldr (\x => \zs => go x zs) (const []) xs0 n
  where
  go : a -> (Nat -> List a) -> Nat -> List a
  go x _ Z = []
  go x k (S n) = x :: k n


filter' : (a -> Bool) -> List a -> List a
filter' p Nil = Nil
filter' p (x :: xs) = if p x then x :: filter' p xs else Nil

filter'2 : (a -> Bool) -> List a -> List a
filter'2 p xs = foldr (\x => \zs => if p x then x :: zs else Nil) Nil xs

||| Insert a value into descending list preserving sorting order.
insSorted : Ord a => a -> List a -> List a
insSorted y [] = [y]
insSorted y xs@(_ :: ts) = foldr go (const []) xs ts
  where
    go : a -> (List a -> List a) -> List a -> List a
    go x k [] = if x >= y then [x, y] else [y, x]
    go x k xs@(_ :: ts) = if x >= y then x :: k ts else y :: x :: xs

||| Ex 7.
-- Here foldr with 'insSorted' is essentially just a re-implementation of a
-- 'sort' call on entire list.
top_ten : Ord a => List a -> List a
-- Build values in the accumulator.
--top_ten = take 10 . foldr insSorted []
-- Build top values in the argument.
--top_ten xs = foldr (\x => \k => \ys => k (take 10 $ insSorted x ys)) id xs xs
top_ten xs = foldr (\x => \k => k . take 10 . insSorted x) id xs xs

||| Ex 8.
over_length : Nat -> List String -> Nat
over_length n xs = foldr (\s => \z => if length s > n then z + 1 else z) Z xs

||| Ex 9.
repl_counts : IO ()
repl_counts = repl "Enter a string: " (show . counts)

main : IO ()
main = repl_counts
