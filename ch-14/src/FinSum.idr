
import Data.Fin
import Data.Nat


%default total

data Sum : Nat -> Type where
  MkSum : (m : Nat) -> (k : Nat) -> Sum (m + k)
  NoSum : (n : Nat) -> Sum n

viewAsSum : (n : Nat) -> (m : Nat) -> Sum n
viewAsSum Z Z = MkSum Z Z
viewAsSum Z (S m') = NoSum Z
viewAsSum (S n') Z = let r = MkSum Z (S n') in r
viewAsSum (S n') (S m') =
  let r = viewAsSum n' m'
  in case r of
          -- `Sum` type having only resulting value as the index (type
          -- parameter) does not tell anything about _how exactly_ `n` is
          -- represented in a view. I.e. though covering function takes second
          -- component `m`, but `Sum` type itself does _not_ require it to be
          -- actually used!
          -- That means, following definition will also satisfy type-checker, but it's
          -- wrong: it'll represent any `n` as `0 + n` ignoring `m` argument.
          --MkSum m' k => let r = MkSum m' (S k) in rewrite plusSuccRightSucc m' k in r
          MkSum m' k => MkSum (S m') k
          NoSum n' => NoSum (S n')

f : Nat -> Nat -> Int
f n m with (viewAsSum n m)
  f (m' + k) m | MkSum m' k = 1
  f n2 m | NoSum n2 = 2

-- To fix above problem, i may add second component `m` as view index. This
-- will require covering function to actually use it in a sum representation.
data Sum2 : Nat -> Nat -> Type where
  MkSum2 : (m : Nat) -> (k : Nat) -> Sum2 (m + k) m
  NoSum2 : (n : Nat) -> Sum2 n m

viewAsSum2 : (n : Nat) -> (m : Nat) -> Sum2 n m
viewAsSum2 Z Z = MkSum2 Z Z
viewAsSum2 Z (S m') = NoSum2 Z
viewAsSum2 (S n') Z = let r = MkSum2 Z (S n') in r
viewAsSum2 (S n') (S m') =
  let r = viewAsSum2 n' m'
  in case r of
          -- Previous wrong implementation does not compiles:
          --MkSum2 k m' => let r = MkSum2 (S k) m' in r
          --MkSum2 m' k => let r = MkSum2 m' (S k) in rewrite plusSuccRightSucc m' k in r
          MkSum2 m' k => let r = MkSum2 (S m') k in r
          NoSum2 n' => NoSum2 (S n')
  -- Though, it's still possible to define function incorrectly: this will
  -- always return `NoSum2`.
  {-
  let r = viewAsSum2 n' (S m')
  in case r of
          MkSum2 (S m') k => let r = MkSum2 (S m') (S k) in
                                 rewrite plusSuccRightSucc m' k in r
          NoSum2 n' => NoSum2 (S n')
          -}

f2 : Nat -> Nat -> Int
f2 n m with (viewAsSum2 n m)
  f2 (m' + k) m' | MkSum2 m' k = 1
  f2 n2 m | NoSum2 n2 = 2

-- And now the same with `Fin`. `Fin` guarantees, that second component is
-- always lesser, than resulting `n`, so i don't need `NoSum` construtor,
-- but following type won't compile with
--
--      Can't solve constraint between: ?n [no locals in scope] and plus (finToNat m) k.
--
-- The reason is `m : Fin n`, and according to `MkFSum2` result type, it should
-- be `m : Fin (finToNat m + k)`, but Idris won't allow to define `m`'s type
-- through `m` itself.
--
-- But this is only part of a problem. Another part is that such definition is
-- actually incorrect, because user may supply any value `k` for constructor,
-- e.g.
--
--      MkFSum2 {n = 4} (FS FZ) 1
--      MkFSum2 {n = 4} (FS FZ) 2
--      MkFSum2 {n = 4} (FS FZ) 3
--
-- but only the last one is actually correct. I.e. because `k` is
-- constructor's _argument_ it's the user who determines the value, therefore
-- there is no guarantee, that he always chooses correct value `k` for which
-- `n === finToNat m + k` holds.
--data FSum2 : (n : Nat) -> Fin n -> Type where
--  MkFSum2 : (m : Fin n) -> (k : Nat) -> FSum2 (finToNat m + k) m

-- So, since user supplies second sum component, i should require, that he
-- _also_ supplies the proof, that this component indeed satisfies the equation.
data FSum : (n : Nat) -> Fin n -> Type where
  MkFSum : (m : Fin n) -> (k : Nat) -> (prf : n = finToNat m + k) -> FSum n m

viewAsFSum : {n : Nat} -> (m : Fin n) -> FSum n m
viewAsFSum {n = S n'} FZ = MkFSum FZ (S n') Refl
viewAsFSum {n = S n'} (FS m') with (viewAsFSum m')
  viewAsFSum {n = S n'} (FS m2) | MkFSum m2 k prf = MkFSum (FS m2) k (cong S prf)

-- It will works, but there's a problem..
g : {n : Nat} -> (m : Fin n) -> Int
g {n = n} m with (viewAsFSum m)
  -- ..to actually reify pattern, i need to pattern match on Refl..
  --g {n = n} m | MkFSum {n = n} m k Refl = ?y1
  --
  -- which also reifies `m : Fin n` to `m : Fin (finToNat m + k)`, but it's
  -- impossible to define type of `m` through itself (the same problem again):
  --
  --    Can't solve constraint between: ?n [no locals in scope] and plus (finToNat ?m) ?k.
  --
  -- The solution is to hide `m` in `finToNat m` behind another pattern
  -- (from https://idris-lang.zulipchat.com/#narrow/channel/556789-help/topic/.E2.9C.94.20View.20Nat.20as.20a.20sum.20of.20Fin.20and.20a.20remainder/with/635151262):
  g {n = n} m | MkFSum {n = n} m k prf with 0 (finToNat m) proof 0 qrf
    -- and now if i pattern match on `Refl`, it reifies `n` to `r + k` and `m`
    -- to `m : Fin (r + k)`, and there's no recursive definition!
    g {n = r + k} m | MkFSum {n = r + k} m k Refl | r = 1

-- I may also try to define `FinSum` _without_ binding resulting sum to
-- particular `Fin` (in essence, similar to `Sum`). But now, first,
-- i need `NoFSum` again, because sine sum is not bound to `Fin`'s index, it
-- may too small for given `Fin`. In fact, i loose all benefits of having
-- `Fin` instead of plain `Nat` in the first place!
data FSum3 : (n : Nat) -> Fin p -> Type where
  MkFSum3 : (m : Fin n) -> (k : Nat) -> FSum3 (finToNat m + k) m
  NoFSum3 : FSum3 n m

viewAsFSum3 : (n : Nat) -> (m : Fin p) -> FSum3 n m
viewAsFSum3 Z _ = NoFSum3
viewAsFSum3 (S n') FZ = MkFSum3 FZ (S n')
viewAsFSum3 (S n') (FS t) =
  case viewAsFSum3 n' t of
       MkFSum3 t k => MkFSum3 (FS t) k
       NoFSum3 => NoFSum3

-- And second, i again hit the same error from recursive definition
-- `m : Fin (finToNat m + k)` and now i can't workaround it, because i can't
-- defer reify of `n` as i did in `g` by not matching on `Refl` immediately.
-- I can't match on `finToNat m` beforehand either, because i don't have `m`
-- until i match on `viewAsFSum3` result.
--g3 : {n : Nat} -> (t : Fin n) -> Int
--g3 {n = n} t with (viewAsFSum3 n t)
--  g3 {n = n2} m | MkFSum3 {n = n2} m k = ?z1
--  g3 {n = n} t | NoFSum3 = ?z2

--data FSum2 : (n : Nat) -> Fin n -> Type where
--  MkFSumZ : FSum2 (Z + S n) FZ
--  MkFSumS : {n, m : Nat} -> {t : Fin n} ->
--            (rec : FSum2 (finToNat t + m) t) -> FSum2 (S (finToNat t + m))  (FS t)

