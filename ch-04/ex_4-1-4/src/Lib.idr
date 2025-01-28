module Lib

public export
data BSTree : Type -> Type where
  EmptyBS : Ord a => BSTree a
  NodeBS : Ord a => BSTree a -> a -> BSTree a -> BSTree a

public export
Eq a => Eq (BSTree a) where
  EmptyBS == EmptyBS = True
  EmptyBS == _ = False
  NodeBS _ _ _ == EmptyBS = False
  NodeBS l1 x r1 == NodeBS l2 y r2 = l1 == l2 && x == y && r1 == r2

total insertBS : a -> BSTree a -> BSTree a
insertBS x EmptyBS = NodeBS EmptyBS x EmptyBS
insertBS x t@(NodeBS l y r) = case compare x y of
                               LT => NodeBS (insertBS x l) y r
                               EQ => t
                               GT => NodeBS l y (insertBS x r)

export
total listToTree : Ord b => List b -> BSTree b
listToTree [] = EmptyBS {a = b}
listToTree (x :: xs) = insertBS x (listToTree xs)

total listToTree' : Ord t => List t -> BSTree t
listToTree' xs = go xs EmptyBS
  where
    total go : List b -> BSTree b -> BSTree b
    go [] t = t
    go (x :: xs) t = go xs (insertBS x t)

export
total treeToList : BSTree b -> List b
treeToList EmptyBS = []
treeToList (NodeBS l x r) = treeToList l ++ x :: treeToList r

public export
data Expr = Val Int
          | Add Expr Expr
          | Sub Expr Expr
          | Mult Expr Expr

export
total evaluate : Expr -> Int
evaluate (Val x) = x
evaluate (Add e1 e2) = evaluate e1 + evaluate e2
evaluate (Sub e1 e2) = evaluate e1 - evaluate e2
evaluate (Mult e1 e2) = evaluate e1 * evaluate e2

export
total maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing my = my
maxMaybe mx Nothing = mx
maxMaybe mx@(Just x) my@(Just y) = if x < y then my else mx

||| Represents shapes.
public export
data Shape =    ||| A triangle, with its base length and height
                Triangle Double Double
              | ||| A rectangle, with its length and height
                Rectangle Double Double
              | ||| A circle, with its radius
                Circle Double

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

public export
data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture

export
total biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive (Rectangle _ _)) = Nothing
biggestTriangle (Primitive (Circle _)) = Nothing
biggestTriangle (Primitive p@(Triangle _ _)) = Just (area p)
biggestTriangle (Combine p1 p2) =
   case big1 of
        Nothing => big2
        Just a1 => case big2 of
                        Nothing => big1
                        Just a2 => if a1 < a2 then big2 else big1
  where
    big1 : Maybe Double
    big1 = biggestTriangle p1
    big2 : Maybe Double
    big2 = biggestTriangle p2
biggestTriangle (Rotate _ p) = biggestTriangle p
biggestTriangle (Translate _ _ p) = biggestTriangle p
