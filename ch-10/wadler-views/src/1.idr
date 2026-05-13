
import Data.Nat
import Data.Vect
import Syntax.PreorderReasoning

vAppendNilRightNeutral : {0 n : Nat} -> (xs : Vect n a) ->
                         (rewrite sym (plusZeroRightNeutral n) in xs ++ []) = xs
vAppendNilRightNeutral Nil = Refl
vAppendNilRightNeutral {n = S n'} (x::xs') =
  let rec = (vAppendNilRightNeutral xs')
      result = cong (x::) (vAppendNilRightNeutral xs') in
      --rewrite plusZeroRightNeutral n' in ?b4
      ?b4

----cong : (0 f : t -> u) -> (0 _ : a = b) -> f a = f b
----cong f Refl = Refl
--
----cong2 : (0 f : t -> u) -> (0 _ : a ~=~ b) -> f a ~=~ f b
--cong3 : (0 f : forall t. t -> u) -> (0 _ : a ~=~ b) -> f a === f b
--cong3 f Refl = Refl
--
--cong4 : (0 f : forall t, u. t -> u) -> (0 _ : a ~=~ b) -> f a ~=~ f b
--cong4 f Refl = ?c2
--
--cong5 : (0 f : t -> u) -> (0 g : t' -> u) -> (0 _ : a ~=~ b) -> f a === g b
--cong5 f g eq = ?c3
--
--cong6 : (0 f : t -> u) -> (g : t' -> u') -> (0 _ : a ~=~ b) -> f a ~=~ g b
--
--fff : Vect (plus n' 0) a -> Vect n' a
--
--{-
--congV : (0 f : {0 l, l' : Nat} -> Vect l a -> Vect l' a) ->
--        {xs : Vect l1 a} -> {ys : Vect l2 a} ->
--        (0 _ : xs ~=~ ys) ->
--        {xs' : Vect l1' a} -> {ys' : Vect l2' a} -> {0 _ : xs' = f xs} -> {0 _ : ys' = f ys} ->
--        xs' ~=~ ys'
--        -}
--
--congV : (0 f : {0 l, l' : Nat} -> Vect l a -> Vect l' a) ->
--        (0 _ : xs ~=~ ys) -> f xs ~=~ f ys
--congV f eq = ?c5

ccc2 : {n' : Nat} -> (xs : Vect (plus n' 0) Int) -> Vect n' Int
--ccc2 xs = rewrite sym (plusZeroRightNeutral n') in xs
ccc2 {n'} xs = replicate n' 1

--castHe : {a : t} -> {b : u} -> (f : t -> (a' : u ** a' ~=~ a)) -> a ~=~ b -> (let (a' ** prf) = f a in a' === b)
--castHe {a = a} {b = a} f Refl with (f a)
--  castHe {a = a'} {b = a'} f Refl | (a' ** Refl) = Refl

--castHe : {x : t} -> (f : t -> (x' : u ** x' ~=~ x)) -> (0 _ : x ~=~ y) -> fst (f x) === y
castHe : {x : t} -> {y : u} -> (f : (c : t) -> (x' : u ** x' ~=~ c)) -> (0 _ : x ~=~ y) -> (let (x' ** prf) = f x in x' === y)
castHe f Refl with (f x)
  castHe f Refl | (x' ** Refl) = Refl

castVPlusZ : (zs : Vect (plus n' 0) a) -> (ys : Vect n' a ** ys ~=~ zs)
castVPlusZ zs = (rewrite sym (plusZeroRightNeutral n') in zs ** rewrite plusZeroRightNeutral n' in Refl)
--castVPlusZ zs = (ccc2 zs ** rewrite plusZeroRightNeutral n' in Refl)

vAppendNilRightNeutral2 : {0 n : Nat} -> (xs : Vect n a) -> xs ++ [] ~=~ xs
vAppendNilRightNeutral2 Nil = Refl
vAppendNilRightNeutral2 {n = S n'} (x::xs') =
  let rec = (vAppendNilRightNeutral2 xs')
      rec2 : Equal {a = Vect n' a} {b = Vect n' a} (rewrite sym (plusZeroRightNeutral n') in xs' ++ []) xs'
      --rec2 = castHe {t = Vect (plus n' 0) a} {u = Vect n' a} {x = xs' ++ []} {y = xs'} ?b5 rec
      rec2 = castHe {t = Vect (plus n' 0) a} {u = Vect n' a} {x = xs' ++ []} {y = xs'} castVPlusZ rec
      result = cong (x::) rec2
      in rewrite plusZeroRightNeutral n' in result

ttt = vAppendNilRightNeutral2 [1,2,3]

vAppendAssociative : {0 n, m, t : Nat} -> (l : Vect n a) -> (c : Vect m a) -> (r : Vect t a) ->
                     (rewrite sym (plusAssociative n m t) in l ++ (c ++ r)) = (l ++ c) ++r
vAppendAssociative [] c r = Refl
vAppendAssociative {n = S n'} (l'::ls) c r =
  let rec = vAppendAssociative ls c r
  in rewrite (plusAssociative n' m t) in cong (l'::) rec

data SnocVect : Vect n a -> Type where
  EmptyV : SnocVect []
  SnocV : (x : a) -> (xs : Vect m a) -> SnocVect xs -> SnocVect (xs ++ [x])

snocVectHelp : {0 n : Nat} -> {ys : Vect m a} -> (acc : SnocVect ys) -> (xs : Vect n a) -> SnocVect (ys ++ xs)
snocVectHelp acc [] = -- rewrite (rewrite sym (plusZeroRightNeutral m) in vAppendNilRightNeutral2 ys) in
                        ?b1
                      --rewrite plusZeroRightNeutral m in
                      --rewrite vAppendNilRightNeutral ys in
                      --rewrite vAppendNilRightNeutral ys in acc
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

