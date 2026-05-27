
module SnocVect

import Data.Nat
import Data.Vect
import Syntax.PreorderReasoning


public export
data SnocVect : Vect n a -> Type where
  EmptyV : SnocVect []
  SnocV : (x : a) -> (xs : Vect m a) -> SnocVect xs -> SnocVect (xs ++ [x])

export 
Eq (SnocVect xs) where
  _ == _ = True

export
vAppendNilRightNeutral : {0 n : Nat} -> (xs : Vect n a) ->
                         (rewrite sym (plusZeroRightNeutral n) in xs ++ []) = xs
vAppendNilRightNeutral Nil = Refl
vAppendNilRightNeutral {n = S n'} (x::xs') =
  let res = (vAppendNilRightNeutral xs')
      rec = cong (x::) (vAppendNilRightNeutral xs') in
      rewrite plusZeroRightNeutral n' in rec

export
vAppendAssociative : {0 n, m, t : Nat} -> (l : Vect n a) -> (c : Vect m a) -> (r : Vect t a) ->
                     (rewrite sym (plusAssociative n m t) in l ++ (c ++ r)) = (l ++ c) ++r
vAppendAssociative [] c r = Refl
vAppendAssociative {n = S n'} (l'::ls) c r =
  let rec = vAppendAssociative ls c r
  in rewrite (plusAssociative n' m t) in cong (l'::) rec

-- Version based on my version of snocListHelp. Too complex calculations with
-- lengthes.
snocVectHelp' : {0 n : Nat} -> {0 ys : Vect m a} -> (acc : SnocVect ys) -> (xs : Vect n a) -> SnocVect (ys ++ xs)
-- Note, that the order of rewrites does not matter, because 'm + 0' in the
-- result type comes from the result type of 'snocVectHelp'' itself, not from
-- rewrite by 'vAppendNilRightNeutral'.
snocVectHelp' acc [] = rewrite plusZeroRightNeutral m in
                      rewrite vAppendNilRightNeutral ys in acc
snocVectHelp' EmptyV (x::xs') = snocVectHelp' (SnocV x [] EmptyV) xs'
snocVectHelp' {m = m' + 1} {n = S n'} acc@(SnocV z rest _) (x::xs') =
  let r = SnocV x (rest ++ [z]) acc
      rec = snocVectHelp' r xs'
      -- (m' + 1) is length of 'acc' on both sides of equation.
      -- (S n') is length of (x::xs')
      -- (m' + 1) + S n' is length of (ys ++ xs)
      -- '+ 1' in ((m' + 1) + 1) comes from length of new accumulator `r`'s list, which is '(rest ++ [z]) ++ [x]'.
      -- So, (ys ++ xs) has length `(m' + 1) + S n'`
      -- And list of `rec` is '(rest ++ [z]) ++ [x] ++ xs'', i.e. has length `((m' + 1) + 1) + n'`.
      prfPlus : (m' + 1) + S n' === ((m' + 1) + 1) + n'
      prfPlus = Calc $
                  |~ (m' + 1) + S n'
                  ~~ S (m' + 1) + n'
                        ...(sym (plusSuccRightSucc (m' + 1) n'))
                  ~~ S ((m' + 1) + 0) + n'
                        ...(rewrite sym (plusZeroRightNeutral (m' + 1)) in Refl)
                  ~~ (S (m' + 1) + 0) + n'
                        ...(Refl)
                  ~~ ((m' + 1) + 1) + n'
                        ...(rewrite sym (plusSuccRightSucc (m' + 1) 0) in Refl)
  -- Note here also, that the order of rewrites does not matter.
  in rewrite prfPlus in
     rewrite vAppendAssociative (rest ++ [z]) [x] xs' in
             rec

-- And here is version based on Data.List.Views snocList version. Much simpler
-- length calculations.
snocVectHelp : {0 n : Nat} -> {ys : Vect m a} -> (acc : SnocVect ys) -> (xs : Vect n a) -> SnocVect (ys ++ xs)
-- Note, that the order of rewrites does not matter, because 'm + 0' in the
-- result type comes from the result type of 'snocVectHelp' itself, not from
-- rewrite by 'vAppendNilRightNeutral'.
snocVectHelp acc [] = rewrite plusZeroRightNeutral m in
                      rewrite vAppendNilRightNeutral ys in acc
snocVectHelp {n = S n'} acc (x::xs') =
  let r = SnocV x ys acc
      rec = snocVectHelp r xs'
      prfPlus : m + S n' === (m + 1) + n'
      prfPlus = Calc $
                  |~ m + S n'
                  ~~ S (m + n')
                      ...(sym (plusSuccRightSucc m n'))
                  ~~ S (m + 0) + n'
                      ...(rewrite sym (plusZeroRightNeutral m) in Refl)
                  ~~ (m + 1) + n'
                      ...(rewrite sym (plusSuccRightSucc m 0) in Refl)
  -- Note here also, that the order of rewrites does not matter.
  in rewrite prfPlus in
     rewrite vAppendAssociative ys [x] xs' in
             rec

export
snocVect : (xs : Vect n a) -> SnocVect xs
snocVect xs = snocVectHelp EmptyV xs

-- Failed attempts to prove using heterogeneous equality.

-- Cast heterogeneous equality to homogeneous equality.
castHe : {x : t} -> (f : (c : t) -> (x' : u ** x' ~=~ c)) -> (0 _ : x ~=~ y) -> fst (f x) === y
castHe f Refl with (f x)
  _ | (x' ** Refl) = Refl

-- Helper function for using `castHe` with `xs ++ []` vector.
castVPlusZ : (zs : Vect (plus n' 0) a) -> (ys : Vect n' a ** ys ~=~ zs)
castVPlusZ zs = (rewrite sym (plusZeroRightNeutral n') in zs ** rewrite plusZeroRightNeutral n' in Refl)

vAppendNilRightNeutral2 : {0 n : Nat} -> (xs : Vect n a) -> xs ++ [] ~=~ xs
vAppendNilRightNeutral2 Nil = Refl
vAppendNilRightNeutral2 {n = S n'} (x::xs') =
  -- Though, the proof is correct, there is no sense in using '~=~' in type,
  -- because internally i still cast everything to '==='.
  let rec = vAppendNilRightNeutral2 xs'
      rec2 : Equal {a = Vect n' a} {b = Vect n' a} (rewrite sym (plusZeroRightNeutral n') in xs' ++ []) xs'
      rec2 = castHe castVPlusZ rec
      result = cong (x::) rec2
      in rewrite plusZeroRightNeutral n' in result

-- Failed attempts to implement `cong` for heterogeneous equality.

congHe : {c : Type -> Type} -> (f : {t : Type} -> t -> c t) -> (0 _ : x ~=~ y) -> f x ~=~ f y
congHe f Refl = Refl

consTy : Type -> Type
consTy (Vect n a) = Vect (S n) a
consTy ty = ty

-- Can't be used with `Data.Vect.(::) 2`, because type `t` of `f` first
-- argument does not match with `Vect len elem` type of `(::)` first argument:
-- Main> :ti congHe {c = consTy} (Data.Vect.(::) 2)
-- Error: When unifying:
--     Vect ?len ?elem -> Vect (S ?len) ?elem
-- and:
--     t -> consTy t
-- Mismatch between: Vect ?len ?elem and t (implicitly bound at EmptyFC).
--
--ttt = congHe {c = consTy}

congHe2 : {c : {t : Type} -> (0 _ : t) -> Type} -> (f : {t : Type} -> (x' : t) -> c x') -> (0 _ : x ~=~ y) -> f x ~=~ f y
congHe2 f Refl = Refl

consTy2 : {t : Type} -> (0 _ : t) -> Type
consTy2 {t = Vect n a} _ = Vect (S n) a
consTy2 {t} _ = t

-- Useless.
consTy2' : {a : Type} -> {n : Nat} -> (0 _ : Vect n a) -> Type
consTy2' _ = Vect (S n) a

-- The same as above: type `t` of `f` first arg does not match with `Vect l a`
-- type of `(::)` first arg:
-- Main> :ti congHe2 {c = consTy2} (Data.Vect.(::) 2)
-- Error: When unifying:
--     Vect ?len ?elem -> Vect (S ?len) ?elem
-- and:
--     (x' : t) -> consTy2 x'
-- Mismatch between: Vect ?len ?elem and t (implicitly bound at EmptyFC).
--
-- ttt2 = congHe2 {c = consTy2}

-- Impossible to prove, because `p n1` type can't be unified with `p n2`:
-- Error: While processing left hand side of congHe3. Can't solve constraint between: ?p ?n2 and ?p ?n1.
congHe3 : {p : Nat -> Type} -> {x : p n1} -> {y : p n2} ->
           {c : {n : Nat} -> p n -> Type} -> (f : {n : Nat} -> (x' : p n) -> c x') -> (0 _ : x ~=~ y) -> f x ~=~ f y
--congHe3 f {p} {n1} {n2} Refl = ?c1

t2 : {n : Nat} -> (xs : Vect n a) -> (the (Vect (plus n 0) a) (rewrite plusZeroRightNeutral n in xs)) ~=~ xs
t2 xs = rewrite plusZeroRightNeutral n in Refl
--t2 : {a : Type} -> {n : Nat} -> (xs : Vect (plus n 0) a) -> (ys : Vect n a) ->
--     (rewrite sym (plusZeroRightNeutral n) in xs) === ys ->
--     xs ~=~ ys
--t2 {n} xs xs Refl = ?b3

vAppendNilRightNeutral2' : {0 n : Nat} -> (xs : Vect n a) -> xs ++ [] ~=~ xs
vAppendNilRightNeutral2' Nil = Refl
vAppendNilRightNeutral2' {n = S n'} (x::xs') =
  case vAppendNilRightNeutral2' xs' of
    -- Can't match with Refl, because
    -- Error: ... Can't solve constraint between: ?_ [no locals in scope] and plus ?_ 0.
    -- and if this ever can be fixed, only by casting everything to '==='
    -- again. Which eliminates any sense in using '~=~' in type in the first
    -- place.
    --Refl => ?c1
    eq => ?not_impl_vAppendNilRightNeutral2_1
