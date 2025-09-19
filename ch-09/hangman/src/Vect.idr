
module Vect

import Decidable.Equality
import Data.Vect
import Data.Vect.Elem

public export
data Subset : Vect n a -> Vect m b -> Type where
  EmptySubset : Subset [] ys
  AddElem : Elem x ys -> Subset xs ys -> Subset (x::xs) ys
  ExpandSet : Subset xs ys -> Subset xs (y::ys)

export
subsetElem : Subset (x::xs) ys -> Elem x ys
subsetElem (AddElem e _) = e
subsetElem (ExpandSet sub) = There (subsetElem sub)

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
