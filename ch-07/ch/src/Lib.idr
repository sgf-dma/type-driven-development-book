module Lib

public export
data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

eval : (Neg num, Integral num, Abs num) => Expr num -> num
eval (Val num) = num
eval (Add e1 e2) = eval e1 + eval e2
eval (Sub e1 e2) = eval e1 - eval e2
eval (Mul e1 e2) = eval e1 * eval e2
eval (Div e1 e2) = eval e1 `div` eval e2
eval (Abs e1) = abs (eval e1)

export
Num num => Num (Expr num) where
  fromInteger = Val . fromInteger
  (+) = Add
  (*) = Mul

export
Neg num => Neg (Expr num) where
  --negate = Sub (Val 0)
  negate x = (0 - x)
  (-) = Sub

export
Num num => Abs (Expr num) where
  abs = Abs

export
Neg num => Integral (Expr num) where
  div = Div
  x `mod` y = x - x `div` y

-- Exercise 7.2.1
export
Show num => Show (Expr num) where
  showPrec _ (Val num) = "V" ++ showPrec App num
  showPrec d (Add e1 e2) = showParens (d >= User 8) $ showPrec (User 8) e1 ++ " + " ++ showPrec (User 8) e2
  showPrec d (Sub e1 e2) = showParens (d >= User 8) $ showPrec (User 8) e1 ++ " - " ++ showPrec (User 8) e2
  showPrec d (Mul e1 e2) = showParens (d >= User 9) $ showPrec (User 9) e1 ++ " * " ++ showPrec (User 9) e2
  -- Any 'User' precedence is greater, than 'Backtick', thus division will be
  -- in braces, even if it's part of a sum.
  showPrec d (Div e1 e2) = showParens (d >= Backtick) $ showPrec Backtick e1 ++ " `div` " ++ showPrec Backtick e2
  showPrec d (Abs e) = "abs(" ++ showPrec Open e ++ ")"

-- Exercise 7.2.2
export
(Neg num, Integral num, Abs num, Eq num) => Eq (Expr num) where
  e1 == e2 = eval e1 == eval e2

-- Exercise 7.2.3
export
(Neg num, Integral num, Abs num) => Cast (Expr num) num where
  cast = eval

(Neg num, Integral num, Abs num) => Cast num (Expr num) where
  cast = Val

-- Exercise 7.3.1
export
Functor Expr where
  map f (Val n) = Val (f n)
  map f (Add e1 e2) = Add (map f e1) (map f e2)
  map f (Sub e1 e2) = Sub (map f e1) (map f e2)
  map f (Mul e1 e2) = Mul (map f e1) (map f e2)
  map f (Div e1 e2) = Div (map f e1) (map f e2)
  map f (Abs e) = Abs (map f e)

data Tree a = Empty
            | Node (Tree a) a (Tree a)

Foldable Tree where
  foldr go acc0 Empty = acc0
  foldr go acc0 (Node l e r) = go e (foldr go (foldr go acc0 l) r)

-- Exercise 7.3.2
public export
data Vect : Nat -> Type -> Type where
  Nil : Vect 0 a
  (::) : a -> Vect n a -> Vect (S n) a

export
Eq a => Eq (Vect n a) where
  Nil == Nil = True
  (x :: xs) == (y :: ys) = x == y && xs == ys
  _ == _ = False

export
Foldable (Vect n) where
  foldr go acc Nil = acc
  foldr go acc (x :: xs) = go x (foldr go acc xs)
