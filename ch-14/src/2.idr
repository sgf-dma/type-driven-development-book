
import Data.Fin
import Data.Vect
import Data.List

{-
total
f : (xs : List a) -> List (List a)
f [] = []
--f (x::xs') = f (drop 1 (x::xs'))
f (x::xs') with (drop 1 (x::xs')) proof eq
  _ | ys = let r = f ys in ?d1

f2 : {l : Nat} -> (xs : List a) -> {auto prf : l = length xs} -> List (List a)
f2 [] = []
f2 (x::xs') {l = S l'} =
  let r = f2 {l = l'} {prf = injective prf} (drop 1 (x::xs'))
  in r
  -}

total
g1 : {0 n : Nat} -> Fin n -> Int
g1 FZ = 1
g1 {n = S n'} (FS t) = g1 t

partial
g2 : {0 n : Nat} -> Fin n -> Int
g2 FZ = 1
g2 {n = S n'} (FS t) = g2 (weaken t)

-- f1 does not change argument.
total
f1 : Nat -> Nat
f1 Z = Z
f1 (S t) = S t

partial
g3 : Nat -> Int
g3 Z = 1
g3 (S k) = g3 (f1 k)

-- This is essentially `f1` written as type.
data F1 : Nat -> Type where
  MkZ : F1 Z
  MkS : (t : Nat) -> F1 (S t)

viewF1 : (n : Nat) -> F1 n
viewF1 Z = MkZ
viewF1 (S t) = MkS t

total
g3a : Nat -> Int
g3a Z = 1
g3a (S k) with (viewF1 k)
  g3a (S Z) | MkZ = g3a 0
  g3a (S (S t)) | MkS t = g3a (S t)

total
g3b : (n : Nat) -> {l : Nat} -> {auto prf : n = l} -> Int
g3b Z = 1
g3b (S k) {l = S Z} {prf = prf} =
  let p' = injective prf
      r = g3b (f1 k) {l = Z} {prf = rewrite p' in Refl}
  in r
g3b (S k) {l = S (S t)} {prf = prf} =
  let p' = injective prf
      r = g3b (f1 k) {l = S t} {prf = rewrite p' in Refl}
  in r

-- f2 changes argument.
total
f2 : Nat -> Nat
f2 Z = Z
--f2 (S t) = t
f2 (S Z) = Z
f2 (S (S t)) = S t

partial
g4 : Nat -> Int
g4 Z = 1
g4 (S k) = g4 (f2 k)

-- Type definition should represent function: function's argument is type argument,
-- constructor with its arguments is resulting value. I.e. Mk2Z0 is 0 for `Z`,
-- Mk2Z1 is 0 for `S Z`, and `Mk2S t` is `S t` for `S (S t)` branch.
data F2 : Nat -> Type where
  Mk2Z0 : F2 Z
  Mk2Z1 : F2 (S Z)
  Mk2S : (t : Nat) -> F2 (S (S t))

viewF2 : (n : Nat) -> F2 n
viewF2 Z = Mk2Z0
viewF2 (S Z) = Mk2Z1
viewF2 (S (S t)) = Mk2S t

total
g4a : Nat -> Int
g4a Z = 1
g4a (S k) with (viewF2 k)
  g4a (S Z) | Mk2Z0 = g4a 0
  g4a (S (S Z)) | Mk2Z1 = g4a 1
  g4a (S (S (S t))) | Mk2S t = g4a (S t)





--data WeakView : (m : Nat) -> Fin m -> Type where
--  MkWZ : {m : Nat} -> WeakView (S (S m)) FZ
--  MkWS : (w : WeakView m t) -> WeakView (S m) (FS t)

data WeakView : (m : Nat) -> Fin m -> Type where
  MkWZ : {m : Nat} -> WeakView (S (S m)) FZ
  MkWS : (w : WeakView m t) -> WeakView (S m) (FS t)

--weakView : (t : Fin n) -> WeakView n t
--weakView FZ = ?x1
--weakView (FS t) = ?x2

--g2a : {0 n : Nat} -> Fin n -> Int
--g2a FZ = 1
--g2a (FS t) with (viewWeak t)
--  g2a (FS FZ) | MkWZ = ?x1
--  g2a (FS (FS m)) | MkWS k =
--    let r = g2a k -- k ~ weaken t
--    in ?x2
--  -- g2 (weaken t)

total
minFin : Fin n -> Nat
minFin FZ = 1
minFin (FS k) = S (minFin k)

total
minFinWeakNeutral : (t : Fin n) -> minFin (weaken t) = minFin t
minFinWeakNeutral FZ = Refl
minFinWeakNeutral (FS t') = cong S (minFinWeakNeutral t')

total
g2b : (t : Fin n) -> {l : Nat} -> {auto prf : minFin t = l} -> Int
g2b FZ = 1
g2b (FS t) {l = S l'} {prf = prf'} =
  let p' = injective prf'
      r = g2b (weaken t) {l = l'}
              {prf = rewrite minFinWeakNeutral t in
                     rewrite p' in Refl}
  in r


--total
--g4 : Nat -> Int
--g4 Z = 1
--g4 (S k) with (k) proof eq
--  _ | Z = 1
--  _ | S t = let r = f1 (S t) in ?a2 -- g4 (f1 (S t))
--
--total
--g5 : Nat -> Int
--g5 Z = 1
--g5 (S k) with (f1 k) proof eq
--  _ | Z = 1
--  _ | S t = ?b2
--
--total
--g5' : Nat -> Int
--g5' Z = 1
--g5' (S k) with (f1 (S k)) proof eq
--  _ | S t = let prf = injective eq in ?c2 -- g5' t
--
--%tcinline
--total
--g6 : Nat -> Int
--g6 Z = 1
--g6 (S k) = g6 Z

