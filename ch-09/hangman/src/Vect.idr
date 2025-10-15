
module Vect

import Decidable.Equality
import Data.Nat
import Data.Vect
import Data.Vect.Elem

%default total

public export
data Subset : Vect n a -> Vect m b -> Type where
  EmptySubset : Subset [] ys
  AddElem : Elem x ys -> Subset xs ys -> Subset (x::xs) ys
  ExpandSet : Subset xs ys -> Subset xs (y::ys)

export
subsetElem : Subset (x::xs) ys -> Elem x ys
subsetElem (AddElem e _) = e
subsetElem (ExpandSet sub) = There (subsetElem sub)

expandBoth : Subset xs xs -> Subset (x::xs) (x::xs)
expandBoth sub = AddElem Here (ExpandSet sub)

subsetOfItself : (xs : Vect n a) -> Subset xs xs
subsetOfItself [] = EmptySubset
subsetOfItself (x::xs) = expandBoth (subsetOfItself xs)

-- I need different n and m here in order to use this in 'addEmpty' below.
vectInj : {xs : Vect n a} -> {ys : Vect m a} -> xs = ys -> (z::xs) = (z::ys)
vectInj Refl = Refl

-- This predicate is useless, because i can only use '===' equations in
-- `rewrite` (or `replace`).
addEmpty2 : {n : Nat} -> (xs : Vect n a) -> xs ++ [] ~=~ xs
addEmpty2 [] = Refl
addEmpty2 {n = S _} (x::xs) = let r = addEmpty2 xs in vectInj {z = x} r

-- Here is a fixed version of the `addEmpty2` .
addEmpty : {n : Nat} -> (xs : Vect n a) ->
           (rewrite sym (plusZeroRightNeutral n) in xs ++ []) = xs
addEmpty [] = Refl
addEmpty {n = S k} (x::xs) =
  rewrite (addEmpty xs)
  in rewrite plusZeroRightNeutral k
  in Refl
  -- This will also work
  --rewrite plusZeroRightNeutral k in vectInj {z = x} (addEmpty xs)

vect_induction :
    (prop : forall n. Vect n a -> Type) ->
    (prop Nil) ->
    (forall k. {ys : Vect k a} -> prop ys -> (y : a) -> prop (y::ys)) ->
    (xs : Vect m a) ->
    prop xs
vect_induction prop pNil pRec [] = pNil
vect_induction prop pNil pRec (x::xs) = pRec (vect_induction prop pNil pRec xs) x

-- Or with replace and explicit induction
addEmpty3 : {n : Nat} -> (xs : Vect n a) ->
            --(replace {p = \t => Vect t a} (plusZeroRightNeutral n) (xs ++ []) = xs)
            (replace (plusZeroRightNeutral n) (xs ++ []) = xs)
addEmpty3 xs = vect_induction prop Refl propRec xs
  where
    prop : forall k. (ys : Vect k a) -> Type
    prop ys = (replace {p = \t => Vect t a} (plusZeroRightNeutral k) (ys ++ [])) === ys
    propRec : forall k. {ys : Vect k a} -> prop ys -> (y : a) -> prop (y::ys)
    propRec rec y =
      -- Ugh, it seems too difficult to write `p` and replace this `rewrite`
      -- with `replace`, so leave it as is..
      rewrite plusZeroRightNeutral k in
              replace {p = \t => y::t = y::ys} (sym rec) Refl

export
reduceSubset :  Subset (x::xs) ys -> Subset xs ys
reduceSubset (AddElem _ sub) = sub
reduceSubset (ExpandSet sub) = ExpandSet (reduceSubset sub)

export
isSubset : DecEq a => (xs : Vect n a) -> (ys : Vect m a) -> Dec (Subset xs ys)
isSubset [] ys = Yes EmptySubset
isSubset (x::xs) ys =
  case isElem x ys of
       No notFound => No $ \sub => notFound (subsetElem sub)
       Yes found => case isSubset xs ys of
                         No notSubset => No $ \sub => notSubset (reduceSubset sub)
                         Yes sub => Yes (AddElem found sub)

insertElem : {xs : Vect n a} -> {zs : Vect m a} ->
             Elem z ys -> Subset (xs ++ zs) ys -> Subset (xs ++ (z::zs)) ys
insertElem {xs = Nil} e sub = AddElem e sub
insertElem {xs = (x::xs)} e sub =
  let r = insertElem e (reduceSubset sub)
  in  AddElem (subsetElem sub) r

-- See different implementation in List.idr.
append : {xs : Vect n a} -> {ys : Vect m a} -> {zs : Vect k a} ->
         Subset xs zs -> Subset ys zs -> Subset (xs ++ ys) zs
append {xs = Nil} sub1 sub2 = sub2
-- I can't use 'addEmpty' for rewrite, because it uses heterogeneous equality.
append {xs = (x::xs)} sub1 sub2 =
  let r = append (reduceSubset sub1) sub2
  in  AddElem (subsetElem sub1) r

snocElem : {xs : Vect n a} -> Elem v ys -> Subset xs ys -> Subset (xs `snoc` v) ys
snocElem {xs = Nil} e sub = AddElem e sub
snocElem {xs = (x::xs)} e sub =
  let r = snocElem e (reduceSubset sub)
  in AddElem (subsetElem sub) r

export
dropSubsetElem : {xs : Vect (S n) a} -> {ys : Vect m a} ->
                 Subset xs ys ->
                 (el : Elem z xs) ->
                 Subset (dropElem xs el) ys
dropSubsetElem (AddElem _ sub) Here = sub
dropSubsetElem {xs = (x::[])} (AddElem e sub) (There {y = x} later) impossible
dropSubsetElem {xs = (x::(_::_))} (AddElem e sub) (There {y = x} later) =
  AddElem e (dropSubsetElem sub later)
dropSubsetElem sub@(ExpandSet _) Here = reduceSubset sub
dropSubsetElem {xs = []} sub@(ExpandSet _) (There _) impossible
dropSubsetElem {xs = x::[]} sub@(ExpandSet _) (There {y = x} _) impossible
dropSubsetElem {xs = x::(_::_)} sub@(ExpandSet _) (There {y = x} later) =
  let e = (subsetElem sub)
  in  AddElem e (dropSubsetElem (reduceSubset sub) later)

transElem : {0 x : a} -> Elem x ys -> Subset ys zs -> Elem x zs
transElem Here sub = subsetElem sub
transElem (There later) sub = transElem later (reduceSubset sub)

trans : {0 xs : Vect n a} -> {0 ys : Vect m a} -> {0 zs : Vect k a} ->
        Subset xs ys -> Subset ys zs -> Subset xs zs
trans EmptySubset _ = EmptySubset
trans (AddElem e sub) sub2 = AddElem (transElem e sub2) (trans sub sub2)
trans (ExpandSet sub) sub2 = trans sub (reduceSubset sub2)
