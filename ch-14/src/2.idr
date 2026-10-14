
import Data.Fin
import Data.Vect
import Data.List
import Decidable.Equality


-- 1. Let's take simple recursive function, which is obviously total:
total
g0 : {0 n : Nat} -> Fin n -> Int
g0 FZ = 1
g0 {n = S n'} (FS t) = g0 t

-- And some other function, which (now) does nothing to its argument.
total
f1 : Nat -> Nat
f1 Z = Z
f1 (S t) = S t

-- Then applying `f1` to `g1`'s argument in recursive calls makes `g1` to no
-- longer be total.
partial
g1 : Nat -> Int
g1 Z = 1
g1 (S k) = g1 (f1 k)

-- Matching on `f1`'s argument in `g1` does not help.
partial
g1' : Nat -> Int
g1' Z = 1
g1' (S Z) = g1' (f1 Z)
g1' (S (S t)) = g1' (f1 (S t))

-- So, generally, there're two strategies to fix this:
--  - use decreasing metric. It may be implemented using recursive view,
--  where decreasing metric will be recursive view's argument,
--  - or use a view refining part of original argument and then use refined
--  part as argument to recursive call. In this case, view just proves, that
--  this part of original argument is indeed the result of nested function
--  call in `g`'s argument.
--
-- The first method is probably better, the second is more tricky and awkward.

total
g1a : (n : Nat) -> {l : Nat} -> {auto prf : n = l} -> Int
g1a Z = 1
g1a (S k) {l = S Z} {prf = prf} =
  let p' = injective prf
      -- Now `l` guarantees totality and `f1 k` argument does not matter in
      -- totality caluclations. It may be any.
      r = g1a (f1 k) {l = Z} {prf = rewrite p' in Refl}
  in r
g1a (S k) {l = S (S t)} {prf = prf} =
  let p' = injective prf
      r = g1a (f1 k) {l = S t} {prf = rewrite p' in Refl}
  in r

-- For a view to refine original function's argument, it must have a type
-- dependent on original argument value. That way matching on a constructor
-- will refine type argument, which in turn will refine original function's
-- argument itself.
--
-- Here view is essentially `f1` written as type. It should be read from right
-- to left:
--
--      MkZ <- F1 Z
--      ...
--       Z  =  f1 Z
--
-- is branch
--
--      f1 Z = Z
--
-- and
--
--      MkS (t : Nat) <- F1 (S t)
--      ............
--          S t        = f1 (S t)
--
-- is branch
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
g1b : Nat -> Int
g1b Z = 1
g1b (S k) with (viewF1 k)
  g1b (S Z) | MkZ = g1b 0
  -- View _refined_ original argument and here by calling `g1b` with _refined
  -- part of original argument_ i essentially translate back from the view
  -- (i.e. result of function `f1`) to the (part of) original argument.
  --
  -- Here the problem is solved by essentially eliminating nested function
  -- call `f1 k` and substituting its result on its place.
  g1b (S (S t)) | MkS t = g1b (S t)

-- 2. Now, f2 changes its argument.
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

total
g2a : (n : Nat) -> {l : Nat} -> {auto prf : n = l} -> Int
g2a Z = 1
g2a (S Z) {l = S Z} {prf} = g2a Z
g2a (S (S Z)) {l = S (S Z)} {prf} = g2a (S Z)
g2a (S (S (S n'))) {l = S (S (S l'))} {prf} =
  -- Value of `l` should be the result of nested function call `f2 k`,
  -- otherwise i can't construct a proof. So in this aspect this method does
  -- not differ from "view" method: i should construct a result of nested
  -- function call by some way and it should be visible to Idris, that it's
  -- smaller.
  let r = g2a (f2 (S (S n'))) {l = (S l')}
              {prf = rewrite injective (injective prf) in
                             Refl}
  in r

-- Note though, that only strictly smaller argument is relevant for totality.
-- Binding `l` (in essense, this is `fuel`) to the result of nested function
-- call is needed to preserve original function semantics.
--
-- Here, number of recursion steps performed is determined by how much fuel i
-- have and fuel quantity is not bound in any way to argument `n`.
total
g2a_wrong : (n : Nat) -> {fuel : Nat} -> Int
g2a_wrong _ {fuel = Z} = 1
g2a_wrong Z {fuel = _} = 1
g2a_wrong (S n') {fuel = Z} = 1
g2a_wrong (S n') {fuel = S fuel'} =
  let r = g2a_wrong (f2 n') {fuel = fuel'}
  in r

-- Again, read view type definition from right to left and data constructors
-- will match to `f2` branches. I have two different `Z` values here, but that
-- does not matter.
data F2 : Nat -> Type where
  Mk2Z0 : F2 Z
  Mk2Z1 : F2 (S Z)
  -- S    t        =  f2 (S (S t))
  Mk2S : (t : Nat) -> F2 (S (S t))

viewF2 : (n : Nat) -> F2 n
viewF2 Z = Mk2Z0
viewF2 (S Z) = Mk2Z1
--  f2 (S (S t)) =    S t
viewF2 (S (S t)) = Mk2S t

total
g2b : Nat -> Int
g2b Z = 1
g2b (S k) with (viewF2 k)
  g2b (S Z) | Mk2Z0 = g2b 0
  g2b (S (S Z)) | Mk2Z1 = g2b 1
  g2b (S (S (S t))) | Mk2S t = g2b (S t)

-- 2. And now recursive function. The main difference of recursive function
--    from previous two is that now result can't be directly calculated,
--    because it contains recursive call.
total
f3 : Nat -> Nat
f3 Z = Z
f3 (S Z) = Z
f3 (S (S t)) = S (f3 (S t))

partial
g3 : Nat -> Int
g3 Z = 1
g3 (S k) = g3 (f3 k)

-- Well, this is correct, but i still need to build `prf2` at `g3a'` call time,
-- which won't be obvious.
total
g3a' : (n : Nat) -> {l : Nat} -> {auto prf1 : l = n} -> {auto prf2 : n = f3 (S n)} -> Int
g3a' Z {l = Z} = 1
g3a' (S Z) {l = S Z} = g3a' Z
g3a' (S (S n')) {l = S (S l')} {prf1} {prf2} =
  let r = g3a' (f3 (S n')) {l = l'}
              {prf1 = rewrite injective (injective prf1) in injective (injective prf2)}
              {prf2 = rewrite sym (injective prf2) in Refl}
  in r

-- Actually, this lemma expresses result of nested function call in terms of
-- `n`. The same trick as before. I need it for constructing `prf2` in `g3a'`
-- call and for (better) versions below.
total
f3Lemma : (n : Nat) -> n = f3 (S n)
f3Lemma Z = Refl
f3Lemma (S n') = let rec = f3Lemma n' in cong S rec

-- I need `l` to be a decreasing argument for totality calculation as before.
total
g3a : (n : Nat) -> {l : Nat} -> {auto prf : l = n} -> Int
g3a Z {l = Z} = 1
g3a (S Z) {l = S Z} = g3a Z
g3a (S (S n')) {l = S (S l')} {prf} =
  let r = g3a (f3 (S n')) {l = l'}
              {prf = rewrite injective (injective prf) in f3Lemma n'}
  in r

-- Or..
total
g3a2 : (n : Nat) -> {l : Nat} -> {auto prf : f3 n = l} -> Int
g3a2 Z {l = Z} = 1
g3a2 (S Z) {l = Z} = g3a2 Z
g3a2 (S (S Z)) {l = S Z} {prf} = g3a2 (S Z)
g3a2 (S (S n')) {l = S (S l')} {prf} =
  let r = g3a2 (f3 (S n')) {l = l'}
               {prf = rewrite injective prf in sym (f3Lemma l')}
  in r

-- Or i may use LTE
total
neqLteIsLt : {n, m : Nat} -> Not (n = m) -> n `LTE` m -> S n `LTE` m
neqLteIsLt {n = Z} {m = Z} neq _ = void (neq Refl)
neqLteIsLt {n = Z} {m = S m'} _ _ = LTESucc LTEZero
neqLteIsLt {n = S n'} {m = Z} _ _ impossible
neqLteIsLt {n = S n'} {m = S m'} neq (LTESucc lte) =
  let rec = neqLteIsLt (\neq' => neq (cong S neq')) lte
  in  LTESucc rec

-- Also, i can prove this by induction over `n` and `m`. This would be even
-- simpler and won't require `neqLteIsLt` at all (note by Claude).
total
lemma : {n, m : Nat} ->
        (f : Nat -> Nat) -> (mon : {x : Nat} -> f x `LTE` f (S x)) -> n `LTE` m -> f n `LTE` f m
lemma {n} {m} f mon lte with (decEq n m)
  lemma {n = m} {m = m} f mon lte | Yes Refl = reflexive
  _ | No neq with (neqLteIsLt neq lte)
    lemma {n = n} {m = m} f mon lte    | No neq | LTEZero impossible
    lemma {n = n} {m = S m'} f mon lte | No neq | LTESucc lte' =
      let rec = lemma {n = n} {m = m'} f mon lte'
      in  transitive rec (mon {x = m'})

f3Mon : {n : Nat} -> f3 n `LTE` f3 (S n)
f3Mon {n = Z} = LTEZero
f3Mon {n = S n'} = lteSuccRight reflexive

f3Lemma3 : {n, m : Nat} -> n `LTE` m -> f3 n `LTE` f3 m
f3Lemma3 lte = lemma f3 f3Mon lte

-- This is not total, because even though i can derive proof for recursive
-- call, using nested function in proof breaks totality check. To not break
-- totality, i should use `prf'` exactly as proof for recursive call and
-- satisfy types only using `rewrite`-s, but this is not possible, because
-- actual `LTE` values for `prf'` and `prf2`' are different. In other words,
-- i still need fuel.
--total
g3a3 : (n : Nat) -> {auto prf : f3 n `LTE` n} -> Int
g3a3 Z {prf = LTEZero} = 1
g3a3 (S Z) {prf = LTEZero} = g3a3 Z
g3a3 (S (S n')) {prf = LTESucc prf'} =
  let prf2 = f3Lemma3 prf'
      r = g3a3 (f3 (S n')) {prf = prf2}
  in r

total
f3LTE : (n : Nat) -> f3 n `LTE` n
f3LTE Z = LTEZero
f3LTE (S Z) = LTEZero
f3LTE (S (S n')) = LTESucc (f3LTE (S n'))

-- But if i add separate decreasing metric `l` (i.e. fuel), i may use anything
-- i want to derive proof for that metric (proof is required, again, to
-- preserve semantics of original function, not for totality).
total
g3a4 : (n : Nat) -> {l : Nat} -> {auto prf : f3 n `LTE` l} -> Int
g3a4 Z = 1
g3a4 (S Z) {l = l} = g3a4 Z {l = l} {prf = LTEZero}
g3a4 (S (S n')) {l = S l'} {prf = LTESucc prf'} =
  let prf2 = transitive (f3LTE (f3 (S n'))) prf'
      r = g3a4 (f3 (S n')) {l = l'} {prf = prf2}
  in r

-- Or bind metric to argument, which will be even simpler.
total
g3a4' : (n : Nat) -> {l : Nat} -> {auto prf : n `LTE` l} -> Int
g3a4' Z = 1
g3a4' (S Z) {l = l} = g3a4' Z {l = l} {prf = LTEZero}
g3a4' (S n') {l = S l'} {prf = LTESucc prf'} =
  let prf2 = transitive (f3LTE n') prf'
      r = g3a4' (f3 n') {l = l'} {prf = prf2}
  in r

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
g3b' : Nat -> Int
g3b' Z = 1
g3b' (S k) with (viewF3 k)
  g3b' (S Z) | Mk3Z0 = g3b' 0
  g3b' (S (S Z)) | Mk3Z1 = g3b' 0
  -- Both typechecks:
  --
  --g3b' (S (S (S t))) | Mk3S rec = g3b' (S (S t))
  --
  -- and this is expected, because view just refined original argument, and
  -- then i use (part of) original argument in recursive call. But i can use
  -- any part!
  g3b' (S (S (S t))) | Mk3S rec = g3b' (S t)

-- Correct version, but not exactly the same as `g3`..
total
g3b : Nat -> Int
g3b n with (viewF3 n)
  g3b Z | Mk3Z0 = 1
  g3b (S Z) | Mk3Z1 = 1
  -- But here the logic of original `g3` is preserved: i call `g3` recursively
  -- with `F3` recursive argument and actual number passed to `g3` is
  -- restricted by recursive view.
  --
  -- There is one problem, though: in original `g3` nested `f3` in recursive
  -- call was with _smaller_ argument, but here `S t` is the result of
  -- `f3 (S (S t)`, not `f3 (S t)` as it should.
  g3b (S (S t)) | Mk3S rec = g3b (S t) | rec

-- To fix `g3b`, i need to match on `t` further and obtain recursive view
-- argument of needed type.
total
g3b4 : Nat -> Int
g3b4 n with (viewF3 n)
  g3b4 Z | Mk3Z0 = 1
  g3b4 (S Z) | Mk3Z1 = 1
  g3b4 (S (S t)) | Mk3S rec with (t) proof 0 eq
    g3b4 (S (S t)) | Mk3S Mk3Z1 | Z = (g3b4 t | rewrite eq in Mk3Z0)
    g3b4 (S (S t)) | Mk3S (Mk3S rec') | S t' = (g3b4 t | rewrite eq in rec')

-- 4. And, finally, back to original problem:
partial
g7 : {0 n : Nat} -> Fin n -> Int
g7 FZ = 1
g7 (FS t) = g7 {n = n} (weaken t)

total
finToNatWeakNeutral : (t : Fin n) -> finToNat (weaken t) = finToNat t
finToNatWeakNeutral FZ = Refl
finToNatWeakNeutral (FS t') = cong S (finToNatWeakNeutral t')

total
-- Metric (fuel) is `l`, `finToNat` preserves semantics of original `g7`.
g7a : (t : Fin n) -> {l : Nat} -> {auto prf : finToNat t = l} -> Int
g7a {n = 1} FZ = 1
g7a {n = S n'} (FS t) {l = S l'} {prf = prf'} =
  let p' = injective prf'
      r = g7a {n = S n'} (weaken t) {l = l'}
              {prf = rewrite finToNatWeakNeutral t in p'}
  in r

-- Or i may use `LTE` in proof. Note, that it doesn't matter, that i may
-- supply metric value greater, than `finToNat t` at call time. The recursion
-- stops anyway, when argument `t` reaches `FZ`. I don't really care about
-- particular metric value, untill it meets two goals:
-- - it decreases at each recursion step, which guarantees totality
-- - i have a proof, that metric (or fuel) does not end _earlier_, than
-- required by function semantics. But if fuel will still remain, when i
-- decide to stop recursion, doesn't matter at all.
total
g7a2 : (t : Fin n) -> {l : Nat} -> {auto prf : finToNat t `LTE` l} -> Int
g7a2 FZ = 1
g7a2 (FS t) {l = S l'} {prf = LTESucc lte} =
  g7a2 (weaken t) {l = l'} {prf = rewrite finToNatWeakNeutral t in lte}

data WeakView : {n : Nat} -> Fin n -> Type where
  MkWZ : WeakView FZ
  MkWS : WeakView t -> WeakView (FS t)

total
weakView : (t : Fin n) -> WeakView t
weakView FZ = MkWZ
weakView (FS t) = MkWS (weakView t)

total
weakView2 : (t : Fin n) -> WeakView {n = S n} (weaken t)
weakView2 FZ = MkWZ
weakView2 (FS t) = let rec = weakView2 t in MkWS rec

--data WeakView3 : {n : Nat} -> Fin n -> Fin (S n) -> Type where
--  Mk2WZ : WeakView3 FZ FZ
--  Mk2WS : WeakView3 t p -> WeakView3 (FS t) (FS p)

-- I can't prove this, because `WeakView (weaken t)` and `WeakView t` are
-- _types_, not values.
total
prf7b : (t : Fin n) -> WeakView (weaken t) = WeakView t

-- I may think about proving something like this, but these _values_ are of
-- _different_ type. So i even if i could prove this, it's useless, because i
-- can't use it in rewrite.
prf7b' : (t : Fin n) -> weaken t = t

-- And, moreover, it's still not total.. (may be because `prf7b` is not defined?)
--total
g7b : {0 n : Nat} -> Fin n -> Int
g7b {n = n} k with (weakView k)
  g7b {n = S Z} FZ | MkWZ = 1
  g7b {n = S n'} (FS t) | MkWS rec =
    --let r = (g7b {n = S n'} (weaken t) | rewrite prf7b t in rec)
    let r = (g7b {n = S n'} (weaken t) | ?b3)
    in r

total
prf7b2 : WeakView t -> WeakView (weaken t)
prf7b2 MkWZ = MkWZ
prf7b2 (MkWS w) = let rec = prf7b2 w in MkWS rec

-- Not total as above.. But here the reason is probably, because there is
-- a nested function call on `rec`, which is my decreasing metric.
--total
g7b2 : {0 n : Nat} -> Fin n -> Int
g7b2 {n = n} k with (weakView2 k)
  g7b2 {n = S Z} FZ | MkWZ = 1
  g7b2 {n = S n'} (FS t) | MkWS rec =
    let p' = prf7b2 rec
        --r = (g7b2 {n = S n'} (weaken t) | p')
        r = (g7b2 {n = S n'} (weaken t) | ?a3)
    in r

-- So, i need a view of a Fin, which recursively represents it as its weakened
-- version.
data WeakView3 : {n : Nat} -> Fin n -> Type where
  Mk2WZ : WeakView3 FZ
  Mk2WS : {n' : Nat} -> {t : Fin n'} ->
          (rec : WeakView3 {n = S n'} (weaken {n = n'} t)) ->
          WeakView3 {n = S n'} (FS t)

total
weakView3 : {n : Nat} -> (t : Fin n) -> {l : Nat} -> {auto prf : l = finToNat t} -> WeakView3 t
weakView3 FZ = Mk2WZ
weakView3 (FS t') {l = S l'} {prf} =
  let rec = weakView3 (weaken t') {l = l'}
                    {prf = rewrite injective prf in
                           rewrite finToNatWeakNeutral t' in
                                   Refl}
  in  Mk2WS rec

-- And now it works. But in essence i use the same proof as was in `g7a`, but
-- now its written in view's covering function. So, it's all the same.
total
g7b3 : {n : Nat} -> Fin n -> Int
g7b3 {n = n} k with (weakView3 k {l = finToNat k})
  g7b3 {n = S n'} FZ | Mk2WZ = 1
  g7b3 {n = S n'} (FS t') | Mk2WS rec =
    let r = (g7b3 {n = S n'} (weaken t') | rec)
    in  r
