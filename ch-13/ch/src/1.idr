
data C : Type -> Type where
  A : a -> C ()

data T : Type where
  Do : C a -> (a -> Inf T) -> T

namespace Tns
  export
  (>>=) : C a -> (a -> Inf T) -> T
  (>>=) = Do
  export
  -- Не работает:
  (>>) : C () -> Inf T -> T
  --(>>) : C a -> Inf T -> T
  mx >> my = mx >>= (\_ => my)

total
loop : T
--loop = Do (A 1) (\_ => loop)
loop = Tns.do
  _ <- A 1
  loop

total
data T2 : Type where
  MkT2 : (Int -> (T2 -> T2)) -> T2

total
f : (1 _ : a) -> a
f x = x

g : (x : a) -> a
g x = f x
