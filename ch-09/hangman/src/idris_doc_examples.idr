
-- Below are examples from https://idris2.readthedocs.io/en/latest/proofs/index.html .

import Decidable.Equality

%default total

nat_induction :
    (prop : Nat -> Type) ->
    (prop Z) ->
    ((k : Nat) -> prop k -> prop (S k)) ->
    (x : Nat) ->
    prop x
nat_induction prop p_Z p_S Z = p_Z
nat_induction prop p_Z p_S (S k) = p_S k (nat_induction prop p_Z p_S k)

plus_ind : Nat -> Nat -> Nat
plus_ind n m = nat_induction (\t => Nat) m (\k, k_rec => S k_rec) n

add_zero : (m : Nat) -> m = plus m 0
add_zero m = nat_induction (\x => x = plus x 0)
                Refl
                --(\k, k_rec => rewrite sym (k_rec) in Refl)
                -- is equivalent to
                (\k, k_rec => replace {p = \y => S k = S y} k_rec Refl)
                m

add_succ : (n, m : Nat) -> S (plus n m) = plus n (S m)
add_succ n m = nat_induction (\t => S (plus t m) = plus t (S m))
                  Refl
                  --(\k, k_rec => rewrite k_rec in Refl)
                  -- is equivalent to
                  --(\k, k_rec => replace {p = \y => S y = S (plus k (S m))} (sym k_rec) Refl)
                  -- but i may also substitute other part, like
                  --(\k, k_rec => replace {p = \y => S (S (plus k m)) = S y} k_rec Refl)
                  -- which will be equivalent to
                  (\k, k_rec => rewrite (sym k_rec) in Refl)
                  n

plus_comm : (n : Nat) -> (m : Nat) -> plus n m = plus m n
plus_comm n m = nat_induction (\x => plus x m = plus m x)
                  (add_zero m)
                  (\k, k_rec => rewrite k_rec in add_succ m k)
                  n

p1: Nat -> Type
p1 n = (n=2)

testReplace: (x=y) -> (p1 x) -> (p1 y)
testReplace a b = replace {p = p1} a b
