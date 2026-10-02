
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
g0 : {0 n : Nat} -> Fin n -> Int
g0 FZ = 1
g0 {n = S n'} (FS t) = g0 t

-- f1 does not change argument.
total
f1 : Nat -> Nat
f1 Z = Z
f1 (S t) = S t

partial
g1 : Nat -> Int
g1 Z = 1
g1 (S k) = g1 (f1 k)

partial
g1' : Nat -> Int
g1' Z = 1
g1' (S Z) = g1' (f1 Z)
g1' (S (S t)) = g1' (f1 (S t))

-- This is essentially `f1` written as type. It should be read from right to
-- left:
--
--      MkZ <- F1 Z
--      ...
--       Z  =  f1 Z
--
-- is
--
--      f1 Z = Z
--
-- and
--
--      MkS (t : Nat) <- F1 (S t)
--      ............
--          S t        = f1 (S t)
--
-- is
--
--      f1 (S t) = S t
--
data F1 : Nat -> Type where
  MkZ : F1 Z
  MkS : (t : Nat) -> F1 (S t)

viewF1 : (n : Nat) -> F1 n
viewF1 Z = MkZ
viewF1 (S t) = MkS t

total
g1a : Nat -> Int
g1a Z = 1
g1a (S k) with (viewF1 k)
  g1a (S Z) | MkZ = g1a 0
  -- View _refines_ original argument and here by calling `g1a` with _refined
  -- (part of) original argument_ i essentially translate back from the view
  -- (i.e. result of function `f1`) to (part of) original argument.
  g1a (S (S t)) | MkS t = g1a (S t)

total
g1b : (n : Nat) -> {l : Nat} -> {auto prf : n = l} -> Int
g1b Z = 1
g1b (S k) {l = S Z} {prf = prf} =
  let p' = injective prf
      r = g1b (f1 k) {l = Z} {prf = rewrite p' in Refl}
  in r
g1b (S k) {l = S (S t)} {prf = prf} =
  let p' = injective prf
      r = g1b (f1 k) {l = S t} {prf = rewrite p' in Refl}
  in r

-- f2 changes argument.
total
f2 : Nat -> Nat
f2 Z = Z
--f2 (S t) = t
f2 (S Z) = Z
f2 (S (S t)) = S t

partial
g2 : Nat -> Int
g2 Z = 1
g2 (S k) = g2 (f2 k)

-- View definition should represent function: function's argument is type
-- argument, constructor with its arguments is resulting value. I.e. Mk2Z0 is
-- 0 from `Z` branch, Mk2Z1 is 0 from `S Z` branch, and `Mk2S t` is `S t`
-- from `S (S t)` branch.
data F2 : Nat -> Type where
  Mk2Z0 : F2 Z
  Mk2Z1 : F2 (S Z)
  Mk2S : (t : Nat) -> F2 (S (S t))

viewF2 : (n : Nat) -> F2 n
viewF2 Z = Mk2Z0
viewF2 (S Z) = Mk2Z1
viewF2 (S (S t)) = Mk2S t

total
g2a : Nat -> Int
g2a Z = 1
g2a (S k) with (viewF2 k)
  g2a (S Z) | Mk2Z0 = g2a 0
  g2a (S (S Z)) | Mk2Z1 = g2a 1
  g2a (S (S (S t))) | Mk2S t = g2a (S t)

total
f3 : Nat -> Nat
f3 Z = Z
f3 (S Z) = Z
f3 (S (S t)) = S (f3 (S t))

partial
g3 : Nat -> Int
g3 Z = 1
g3 (S k) = g3 (f3 k)

data F3 : Nat -> Type where
  Mk3Z0 : F3 Z
  Mk3Z1 : F3 (S Z)
  Mk3S : (rec : F3 (S t)) -> F3 (S (S t))

viewF3 : (n : Nat) -> F3 n
viewF3 Z = Mk3Z0
viewF3 (S Z) = Mk3Z1
viewF3 (S (S t)) = Mk3S (viewF3 (S t))

-- Incorrect version.
total
g3a' : Nat -> Int
g3a' Z = 1
g3a' (S k) with (viewF3 k)
  g3a' (S Z) | Mk3Z0 = g3a' 0
  g3a' (S (S Z)) | Mk3Z1 = g3a' 0
  -- Both typechecks:
  --
  --g3a' (S (S (S t))) | Mk3S rec = g3a' (S (S t))
  --
  -- and this is expected, because view just refined original argument, and i
  -- use (part of) original argument in recursive call.
  g3a' (S (S (S t))) | Mk3S rec = g3a' (S t)

-- Correct version.
total
g3a : Nat -> Int
g3a n with (viewF3 n)
  g3a Z | Mk3Z0 = 1
  g3a (S Z) | Mk3Z1 = 1
  -- But here the logic of original `g3` is preserved: i call `g3` recursively
  -- with `F3` recursive argument. And actual number passed to `g3` does not
  -- really matters: `F3` recursive argument restricts this number to
  -- correct value only!
  g3a (S (S t)) | Mk3S rec = g3a (S t) | rec

--total
--f4 : (n : Nat) -> Fin n
--f4 Z = FZ
--f4 (S t) = FS (f4 t)
--
--partial
--g3 : Nat -> Int
--g3 Z = 1
--g3 (S k) = g3 (f3 k)


--data WeakView : (m : Nat) -> Fin m -> Type where
--  MkWZ : {m : Nat} -> WeakView (S (S m)) FZ
--  MkWS : (w : WeakView m t) -> WeakView (S m) (FS t)

total
finToNatWeakNeutral : (t : Fin n) -> finToNat (weaken t) = finToNat t
finToNatWeakNeutral FZ = Refl
finToNatWeakNeutral (FS t') = cong S (finToNatWeakNeutral t')

myw : Fin n -> Fin (S n)
myw FZ = FZ
myw (FS k) = FS (myw k)

data WeakView : {n : Nat} -> Fin n -> Type where
  MkWZ : WeakView FZ
  MkWS : WeakView t -> WeakView (FS t)

weakView : (t : Fin n) -> WeakView t
weakView FZ = MkWZ
weakView (FS t) = MkWS (weakView t)

weakView2 : (t : Fin n) -> WeakView {n = S n} (weaken t)
weakView2 FZ = MkWZ
weakView2 (FS t) = let rec = weakView2 t in MkWS rec

data WeakView2 : {n : Nat} -> Fin n -> Type where
  Mk2WZ : WeakView2 FZ
  Mk2WS : {n' : Nat} -> {t : Fin n'} ->
          (rec : WeakView2 {n = S n'} (weaken {n = n'} t)) ->
          WeakView2 {n = S n'} (FS t)

total
weakView3 : {n : Nat} -> (t : Fin n) -> {l : Nat} -> {auto prf : l = finToNat t} -> WeakView2 t
weakView3 FZ = Mk2WZ
weakView3 (FS t') {l = S l'} {prf} =
  let rec = weakView3 (weaken t') {l = l'}
                    {prf = rewrite injective prf in
                           rewrite finToNatWeakNeutral t' in
                            Refl}
  in  Mk2WS rec
--  weakView3 (FS FZ) | Mk2WZ = Mk2WS ?z1 -- Mk2WS Mk2WZ
--  weakView3 (FS (FS t)) | Mk2WS w = ?z2 -- Mk2WS (Mk2WS ?c2) -- (weakView t)

--data WeakView2 : {n : Nat} -> Fin n -> Fin (S n) -> Type where
--  Mk2WZ : WeakView2 FZ FZ
--  Mk2WS : WeakView2 t p -> WeakView2 (FS t) (FS p)

partial
g7 : {0 n : Nat} -> Fin n -> Int
g7 FZ = 1
g7 (FS t) = g7 {n = n} (weaken t)

total
--g7a : {0 n : Nat} -> Fin n -> WeakView t -> Int
g7a : {0 n : Nat} -> Fin n -> Int
g7a {n = n} k with (weakView k)
  g7a {n = S Z} FZ | MkWZ = 1
  g7a {n = S n'} (FS t) | MkWS rec =
    let r = (g7a {n = S n'} (weaken t) | ?b3)
    in ?b2

total
wWV : WeakView t -> WeakView (weaken t)
wWV MkWZ = MkWZ
wWV (MkWS w) = let rec = wWV w in MkWS rec

total
--g7a2 : {0 n : Nat} -> (t : Fin n) -> WeakView (weaken t) -> Int
g7a2 : {0 n : Nat} -> Fin n -> Int
g7a2 {n = n} k with (weakView2 k)
  g7a2 {n = S Z} FZ | MkWZ = 1
  --g7a2 {n = S (S Z)} (FS FZ) | MkWS MkWZ = ?a5
  --g7a2 {n = S (S n')} (FS (FS t)) | MkWS (MkWS rec) =
  --  let r = (g7a2 {n = S n'} (weaken t) | ?a3)
  --  in ?a2
  g7a2 {n = S n'} (FS t) | MkWS rec =
    let p' = wWV rec
        r = (g7a2 {n = S n'} (weaken t) | ?a3)
    in ?a2

total
g7a3 : {n : Nat} -> Fin n -> Int
g7a3 {n = n} k with (weakView3 k {l = finToNat k})
  g7a3 {n = S n'} FZ | Mk2WZ = 1
  g7a3 {n = S n'} (FS t') | Mk2WS rec =
    let r = (g7a3 {n = S n'} (weaken t') | rec)
    in  r

g7a' : {0 n : Nat} -> Fin n -> Int
g7a' {n = n} k with (weakView (FS k))
  g7a' {n = S Z} FZ | MkWS MkWZ = 1
  g7a' {n = S n'} (FS t) | MkWS (MkWS rec) = g7a' {n = n'} t | (MkWS rec)

total
g7b : (t : Fin n) -> {l : Nat} -> {auto prf : finToNat t = l} -> Int
g7b {n = 1} FZ = 1
g7b {n = S n'} (FS t) {l = S l'} {prf = prf'} =
  let p' = injective prf'
      r = g7b {n = S n'} (weaken t) {l = l'}
              {prf = rewrite finToNatWeakNeutral t in
                     rewrite p' in Refl}
  in r

lteSelf : (n : Nat) -> LTE n n
lteSelf Z = LTEZero
lteSelf (S k) = LTESucc (lteSelf k)

-- This metric is incorrect, because i may choose `m = 1` for any `n` and
-- there'll be no iterations at all.
total
g7b' : {n, m : Nat} -> Fin n -> Fin m -> {auto prf : m `LTE` n} -> Int
g7b' _ FZ = 1
g7b' FZ (FS _) = 2
g7b' {n = S n'} (FS t) (FS k) {prf = prf} =
  g7b' {n = S n'} (weaken t) k {prf = lteSuccLeft prf}

data FinToNatView : {n : Nat} -> Fin n -> Type where
  MkMinFZ : (n' : Nat) -> FinToNatView {n = S n'} FZ
  MkMinFS : (rec : FinToNatView t) -> FinToNatView (FS t)

total
finToNatView : {n : Nat} -> (t : Fin n) -> FinToNatView t
finToNatView {n = S n'} FZ = MkMinFZ n'
finToNatView (FS t) = MkMinFS (finToNatView t)

total
finToNatView2 : {n : Nat} -> (t : Fin n) -> FinToNatView (weaken t)
finToNatView2 {n = S n'} FZ = MkMinFZ (S n')
finToNatView2 (FS t) = let rec = finToNatView2 t in MkMinFS rec

g7b'4 : {n : Nat} -> (t : Fin n) -> Int
g7b'4 {n = S n'} FZ = 1
g7b'4 {n = S n'} (FS t) with (finToNatView t)
  g7b'4 {n = S (S m)} (FS FZ) | MkMinFZ m = ?e4
  g7b'4 {n = S (S m)} (FS (FS t')) | MkMinFS rec =
    let r = g7b'4 {n = S (S m)} ?e6
    in  ?e5

g7b'3 : {n : Nat} -> (t : Fin n) -> FinToNatView (weaken t) -> Int
g7b'3 {n = S n'} FZ (MkMinFZ (S n')) = 1
g7b'3 {n = S n'} (FS t) (MkMinFS rec) =
  --g7b'3 {n = S n'} (weaken t) (rewrite pp t in rec)
  g7b'3 {n = S n'} (weaken t) ?e3

data FinToNatView3 : {n : Nat} -> Fin n -> Type where
  Mk3MinFZ : (n' : Nat) -> FinToNatView3 {n = S n'} FZ
  Mk3MinFS : {n' : Nat} -> {t : Fin n'} ->
             (rec : FinToNatView3 {n = S n'} (weaken t)) ->
             FinToNatView3 {n = S n'} (FS t)

--total
--finToNatView3 : {n : Nat} -> (t : Fin n) -> FinToNatView3 (weaken t)
--finToNatView3 {n = S n'} FZ = ?z1 -- Mk3MinFZ n'
--finToNatView3 (FS t) = let rec = finToNatView3 t in Mk3MinFS ?z2 -- Mk3MinFS rec

total
pp : (t : Fin n) -> FinToNatView (weaken t) = FinToNatView t
--pp FZ = ?y1
--pp (FS t') = let r = pp t' in ?y2

--total
g7b'2 : {n : Nat} -> (t : Fin n) -> FinToNatView t -> Int
g7b'2 {n = S n'} FZ (MkMinFZ n') = 1
g7b'2 {n = S n'} (FS t) (MkMinFS rec) =
  --g7b'2 {n = S n'} (weaken t) (rewrite pp t in rec)
  g7b'2 {n = S n'} (weaken t) ?e2
  --g7b' {n = S n'} k (weaken t) {prf = lteSuccLeft prf} --lteSuccLeft lteSelf}
  --g7b' {n = S n'} t (weaken t) {prf = lteSuccLeft lteSelf}

--total
--g7b'0 : {n : Nat} -> Fin n -> Int
--g7b'0 t = g7b' t t {prf = lteSelf}

--g7b'2 : Fin n -> Fin m -> {auto prf : m `LTE` n} -> Int
--g7b'2 FZ = 1
--g7b'2 (FS FZ) = 1
--g7b'2 {n = S n'} (FS t) (FS k) {prf = prf'} =
--  g7b'2 {n = S n'} (weaken t) t {prf = lteSuccLeft lteSelf}


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

