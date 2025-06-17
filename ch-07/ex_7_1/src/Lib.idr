module Lib

f : (g : (x : a) -> b) -> c

public export
data Shape =    ||| A triangle, with its base length and height
                Triangle Double Double
              | ||| A rectangle, with its length and height
                Rectangle Double Double
              | ||| A circle, with its radius
                Circle Double

export
Eq Shape where
  Triangle b h == Triangle b' h' = b == b' && h == h'
  Rectangle x y == Rectangle x' y' = x == x' && y == y'
  Circle r == Circle r' = r == r'
  _ == _ = False

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

export
Ord Shape where
  compare shape1 shape2 = compare (area shape1) (area shape2)
