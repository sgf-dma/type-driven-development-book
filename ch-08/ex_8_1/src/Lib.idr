module Lib

%default total

myCong : (f : t -> u) -> a = b -> f a = f b
myCong f Refl = Refl {a = u} {x = f a}

-- Ex 1.
same_cons : {x : a} -> {xs : List a} -> {ys : List a}
          -> xs = ys
          -> (x :: xs) = (x :: ys)
--same_cons {a = a} {x = x} z@Refl = let prf = Refl {a = a} {x = x} in myCong2 (::) prf z
same_cons {x = x} prf@Refl = myCong (x ::) prf

-- Ex 2.
myCong2 : (f : t1 -> t2 -> u) -> a = b -> c = d -> f a c = f b d
myCong2 f Refl Refl = Refl {a = u} {x = f a c}

same_list : {x : a} -> {xs : List a} -> {ys : List a}
          -> x = y -> xs = ys
          -> (x :: xs) = (y :: ys)
same_list {x = x} prfX@Refl prfXs@Refl = myCong2 (::) prfX prfXs

-- Ex 3.
data ThreeEq : a -> b -> c -> Type where
  SameThree : {t : Type} -> (a : t) -> ThreeEq a a a

-- Ex 4.
--myTrans : (f : ) -> a = b -> b = c -> f a = f c

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS x x x (SameThree x) = SameThree (S x)
--allSameS x x x (SameThree x) =
--  let prf = myCong S (Refl {x = x})
--  in  ?w3

test : String
test = "Hello from Idris2!"
