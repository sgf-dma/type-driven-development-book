
data T : (ty : Type) -> Nat -> (ty -> Nat) -> Type where
  Bind : T a s1 stateFn2 -> ((r : a) -> T b (stateFn2 r) stateFn3) -> T b s1 stateFn3
  Pure : (res : ty) -> T ty (stateFn res) stateFn

stateFn1 : Int -> Nat
stateFn1 2 = Z
stateFn1 _ = 1

testPure : T Int Z (\x => stateFn1 x)
-- Определение типа ниже не работает, потому что:
--      Warning: We are about to implicitly bind the following lowercase names.
--      You may be unintentionally shadowing the associated global definitions:
--        stateFn1 is shadowing Lib.stateFn1
--
--testPure : T Int Z stateFn1
--testPure = Bind (Pure 2 {stateFn = stateFn1}) (\x => Pure x)
-- Не работает ни с одним вариантом типа.
--testPure = Bind (Pure 2 {stateFn = stateFn1}) (\x => Pure 2 {stateFn = stateFn1})
testPure = Bind (Pure 2 {stateFn = stateFn1}) (\x => ?a1)
