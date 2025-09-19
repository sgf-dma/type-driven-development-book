
module List

import Decidable.Equality
import Data.String
import Data.Vect
import Data.Vect.Elem
import Data.List.Elem

public export
data Subset : List a -> List b -> Type where
  EmptySubset : Subset [] ys
  AddElem : Elem x ys -> Subset xs ys -> Subset (x::xs) ys
  ExpandSet : Subset xs ys -> Subset xs (y::ys)

export
subsetElem : Subset (x::xs) ys -> Elem x ys
subsetElem (AddElem e _) = e
subsetElem (ExpandSet sub) = let later = subsetElem sub in There later

export
reduceSubset :  Subset (x::xs) ys -> Subset xs ys
reduceSubset (AddElem e sub) = sub
reduceSubset (ExpandSet sub) = let r = reduceSubset sub in ExpandSet r

export
isSubset : DecEq a => (xs : List a) -> (ys : List a) -> Dec (Subset xs ys)
isSubset [] ys = Yes EmptySubset
isSubset (x::xs) ys =
  case isElem x ys of
       No notFound => No $ \sub => notFound (subsetElem sub)
       Yes found => case isSubset xs ys of
                         No notSubset => No $ \sub => notSubset (reduceSubset sub)
                         Yes sub => Yes (AddElem found sub)

export
-- Proof, that dropping element from a subset preserves Subset relation.
dropSubsetElem : {0 xs, ys : List a} -> Subset xs ys -> (el : Elem z xs) -> Subset (dropElem xs el) ys
dropSubsetElem EmptySubset _ impossible
dropSubsetElem (AddElem e sub) Here = sub
dropSubsetElem (AddElem e sub) (There later) = let r = dropSubsetElem sub later in AddElem e r
dropSubsetElem sub@(ExpandSet _) Here = reduceSubset sub
dropSubsetElem sub@(ExpandSet _) p@(There {y = x} later) =
  let e = (subsetElem sub)
      r = dropSubsetElem (reduceSubset sub) later
  in  AddElem e r

transElem : {0 x : a} -> Elem x ys -> Subset ys zs -> Elem x zs
transElem Here sub = subsetElem sub
transElem t@(There later) sub = let r = reduceSubset sub in transElem later r

trans : {0 xs, ys, zs : List a} -> Subset xs ys -> Subset ys zs -> Subset xs zs
trans EmptySubset _ = EmptySubset
trans (AddElem e sub) sub2 = AddElem (transElem e sub2) (trans sub sub2)
trans (ExpandSet sub) sub2 = trans sub (reduceSubset sub2)

export
uniqueElems : Eq a => (input : List a) -> List a
uniqueElems input = go input []
  where
    go : List a -> List a -> List a
    go [] acc = acc
    go (x::xs) acc = go xs (if x `elem` acc then acc else acc `snoc` x)

uniqueElems' : Eq a => (input : List a) -> (unique : List a ** Subset unique input)
uniqueElems' input = go input [] {subCur = subsetOfItself input} {subAcc = EmptySubset}
  where
    go : (cur : List a) -> {subCur : Subset cur input} ->
         (acc : List a) -> {subAcc : Subset acc input} ->
         (res : List a ** Subset res input)
    go [] acc {subAcc = subAcc} = (acc ** subAcc)
    go (x::xs) acc {subCur = subCur} {subAcc = subAcc} =
      let subCur' = reduceSubset subCur
      in  case x `elem` acc of
               True => go xs acc {subCur = subCur'} {subAcc = subAcc}
               False => let xEl = subsetElem subCur
                        in go xs (x::acc) {subCur = subCur'} {subAcc = AddElem xEl subAcc}
