module Lib

%default total

myCong : (f : t -> u) -> a = b -> f a = f b
--myCong f Refl = Refl {a = u} {x = f a}
myCong f Refl = Refl

-- Ex 1.
same_cons : {z : a} -> {xs : List a} -> {ys : List a}
          -> xs = ys
          -> (z :: xs) = (z :: ys)
--same_cons {z = z} prf@Refl = myCong (z ::) prf
-- or
--same_cons {z = z} prf@Refl = Refl {a = List a} {x = z :: xs}
-- or just
same_cons {z = z} prf@Refl = Refl

-- Ex 2.
myCong2 : (f : t1 -> t2 -> u) -> a = b -> c = d -> f a c = f b d
--myCong2 f Refl Refl = Refl {a = u} {x = f a c}
myCong2 f Refl Refl = Refl

same_list : {x : a} -> {xs : List a} -> {ys : List a}
          -> x = y -> xs = ys
          -> (x :: xs) = (y :: ys)
--same_list {x = x} prfX@Refl prfXs@Refl = myCong2 (::) prfX prfXs
-- or
--same_list {x = x} Refl Refl = Refl {a = List a} {x = x :: ys}
-- or just
same_list {x = x} Refl Refl = Refl

-- Ex 3.
data ThreeEq : a -> b -> c -> Type where
  --SameThree : {a : Type} -> {x : a} -> ThreeEq x x x
  SameThree : {0 x : a} -> ThreeEq x x x

-- Ex 4.
--myTrans : (f : ) -> a = b -> b = c -> f a = f c

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
--allSameS y y y z@SameThree = SameThree {a = Nat}
-- or
--allSameS y y y z@SameThree = SameThree {x = S y}
-- or
allSameS y y y SameThree = SameThree

