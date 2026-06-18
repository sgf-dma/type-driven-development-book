
module Ch12

import Ch2_3


-- I assume 'Nat' to be a view of 'Integer's.
viewcase : (zero : a) -> (succ : Nat -> a) -> Nat -> a
viewcase zero _     Z = zero
viewcase _    succ (S n) = succ n

zero : Integer
zero = 0

succ : Nat -> Integer
succ n = natToInteger n + 1

-- Version of 'fib' from src/Ch2_3.idr using `viewcase`.
export
fibVc : (m : Nat) -> Integer
fibVc m = viewcase zero (\m' => viewcase (succ Z) (\n => fibVc n + fibVc (S n)) m') m

export
fibx : (a : Integer) -> (b : Integer) -> (m : Nat) -> Integer
fibx a b Z = a
fibx a b (S n) = fibx b (a + b) n

export
fibxVc : (a : Integer) -> (b : Integer) -> (m : Nat) -> Integer
--fibxVc a b m = viewcase a (\n => fibxVc b (a + b) n) m
fibxVc a b m = let f = \n => fibxVc b (a + b) n in viewcase a f m

-- Essentially, this is 'Ext' variant from lambda-lifting examples. And as
-- noted in src/LambdaLifting.idr both attempts 2 and 3 results are the same
-- for non-recrusive 'let'-s.
fibx0 : (a : Integer) -> (b : Integer) -> (n : Nat) -> Integer
fibx0 a b n = fibxVc b (a + b) n

export
fibxVcL : (a : Integer) -> (b : Integer) -> (m : Nat) -> Integer
--fibxVcL a b m = let f = fibx0 a b in viewcase a f m
fibxVcL a b m = viewcase a (fibx0 a b) m

-- So, the problem with above definition has nothing in common with
-- lambda-lifting attempts 2 and 3 (see src/LambdaLifting.idr). The problem
-- probably is not with lazy/strict evaluation and that lambda function, like
-- the one in 'fibxVc2' is not a thunk, but the one in 'fibxVc2L' is.
-- Probably, the problem is with some additional allocations and how they're
-- made in particular compiler implementation. Apart from this, these two
-- definitions 'fibxVc2' and 'fibxVc2L' look completely identical to me.
export
fibxVc2 : (a : Integer) -> (b : Integer) -> (m : Nat) -> Integer
fibxVc2 a b m = viewcase (\a, b => a) (\n, a, b => fibxVc2 b (a + b) n) m a b

fibx1 : (a : Integer) -> (b : Integer) -> Integer
fibx1 a b = a

fibx2 : (n : Nat) -> (a : Integer) -> (b : Integer) -> Integer
fibx2 n a b = fibxVc2 b (a + b) n

export
fibxVc2L : (a : Integer) -> (b : Integer) -> (m : Nat) -> Integer
fibxVc2L a b m = viewcase fibx1 fibx2 m a b
