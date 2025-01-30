module Lib

import Data.Fin

%default partial

||| Represents shapes.
data Shape =    ||| A triangle, with its base length and height
                Triangle Double Double
              | ||| A rectangle, with its length and height
                Rectangle Double Double
              | ||| A circle, with its radius
                Circle Double

data Shape' : Type where
  Triangle' : Double -> Double -> Shape'
  Rectangle' : Double -> Double -> Shape'
  Circle' : Double -> Shape'

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture

rectangle : Picture
rectangle = Primitive (Rectangle 20 10)

circle : Picture
circle = Primitive (Circle 5)

triangle : Picture
triangle = Primitive (Triangle 10 10)

export
testPicture : Picture
testPicture = Combine (Translate 5 5 rectangle)
                (Combine (Translate 35 5 circle) 
                         (Translate 15 25 triangle))

export
pictureArea : Picture -> Double
pictureArea (Primitive shape) = area shape
pictureArea (Combine p1 p2) = pictureArea p1 + pictureArea p2
pictureArea (Rotate _ p) = pictureArea p
pictureArea (Translate _ _ p) = pictureArea p

data Biggest = NoTriangle | Size Double

total biggestTriangle : Picture -> Biggest
biggestTriangle (Primitive (Rectangle _ _)) = NoTriangle
biggestTriangle (Primitive (Circle _)) = NoTriangle
biggestTriangle (Primitive p@(Triangle _ _)) = Size (area p)
biggestTriangle (Combine p1 p2) =
   case big1 of
        NoTriangle => big2
        Size a1 => case big2 of
                        NoTriangle => big1
                        Size a2 => if a1 < a2 then big2 else big1
  where
    big1 : Biggest
    big1 = biggestTriangle p1
    big2 : Biggest
    big2 = biggestTriangle p2
biggestTriangle (Rotate _ p) = biggestTriangle p
biggestTriangle (Translate _ _ p) = biggestTriangle p

data Tree a = Empty
            | Node (Tree a) a (Tree a)

total insert : Ord a => a -> Tree a -> Tree a
insert x Empty = Node Empty x Empty
insert x t@(Node l y r) = case compare x y of
                               LT => Node (insert x l) y r
                               EQ => t
                               GT => Node l y (insert x r)

data BSTree : Type -> Type where
  EmptyBS : Ord a => BSTree a
  NodeBS : Ord a => BSTree a -> a -> BSTree a -> BSTree a

--data BSTree' : Ord a => (a : Type) -> Type where
--  EmptyBS' : Ord a => {a : Type} -> BSTree' a

data PowerSource = Petrol | Pedal

data Vehicle : PowerSource -> Type where
  Bicycle : Vehicle Pedal
  Car : (fuel : Nat) -> Vehicle Petrol
  Bus : (fuel : Nat) -> Vehicle Petrol

total wheels : Vehicle pw -> Nat
wheels Bicycle = 2
wheels (Car _) = 4
wheels (Bus _) = 4

total refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel Bicycle impossible

data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

total append : Vect n a -> Vect m a -> Vect (n + m) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

zip : Vect n a -> Vect n b -> Vect n (a, b)
zip [] [] = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys

data Fin' : (n : Nat) -> Type where
    FZ' : Fin' (S k)
    FS' : Fin' k -> Fin' (S k)

integerToFin' : Integer -> (n : Nat) -> Maybe (Fin' n)
integerToFin' _ Z     = Nothing
integerToFin' x n@(S k) = case compare x 0 of
                               LT => Nothing
                               EQ => Just FZ'
                               GT => FS' <$> integerToFin' (x - 1) k
                               {-
                               GT => case integerToFin' (x - 1) k of
                                          Nothing => Nothing
                                          Just t => Just (FS' t)
                                          -}

index : Fin' n -> Vect n a -> a
index FZ' (x :: xs) = x
index (FS' t) (_ :: xs) = index t xs

tryIndex : {n : Nat} -> Integer -> Vect n a -> Maybe a
tryIndex {n} i xs = case integerToFin' i n of
                     Nothing => Nothing
                     Just fi => Just (index fi xs)

