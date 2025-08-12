
myPlus : (x : Nat) -> (y : Nat) -> Nat
myPlus Z y = y
myPlus (S k) y = S (myPlus k y)

zeroPrf : (n : Nat) -> n = myPlus 0 n

zeroPrf2 : (n : Nat) -> n = myPlus n 0

comPrf : (n, m : Nat) -> plus n m = plus m n

--g : (n, m : Nat) -> Nat
--g n m = case comPrf n m of
--             Refl => 2

f : {m : Nat} -> Nat
f {m = Z} = case zeroPrf2 Z of
                 Refl => 2
f {m = S Z} = case zeroPrf2 (S Z) of
                   Refl => 2
f {m = m} = case zeroPrf2 m of
                 Refl => 2
