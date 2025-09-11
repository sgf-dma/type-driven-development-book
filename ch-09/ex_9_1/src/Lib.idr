module Lib

import Decidable.Equality
import Data.List
import Data.List.Elem

%default total

-- Ex 1.
data MyElem : a -> List a -> Type where
  MyHere : MyElem x (x :: xs)
  MyThere : MyElem x xs -> MyElem x (y :: xs)

-- Ex 2.

data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

Uninhabited (Last [] value) where
  uninhabited LastOne impossible
  uninhabited (LastCons _) impossible

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] _ = No uninhabited
isLast [x] value = case decEq x value of
                        Yes prf => rewrite prf in Yes LastOne
                        No contra => No $ \LastOne => contra Refl
isLast (x::y::xs) value = case isLast (y::xs) value of
                               Yes prf => Yes (LastCons prf)
                               No contra => No $ \(LastCons prf) => contra prf
