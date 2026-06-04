
module Ch7

import Data.Vect


-- This view does not prove, that lengths of left and right are equal. If i
-- need this, it's simpler to use 'Vect' instead. Also, i don't prove, that
-- 'left' is `map fst xs` and 'right' is `map snd xs`, but this should
-- directly follow from parametric polymorphism `zipView`.
public export
data ZipView : List (a, b) -> Type where
  ZPair : {xs : List (a, b)} -> (left : List a) -> (right : List b) -> ZipView xs

export
Eq (ZipView xs) where
  _ == _ = True

export
zipView : (xs : List (a, b)) -> ZipView xs
zipView [] = ZPair [] []
zipView ((l, r)::xs') =
  case zipView xs' of ZPair left right => ZPair (l::left) (r::right)

public export
data ZipVecView : Vect n (a, b) -> Type where
  ZVecPair : {xs : Vect n (a, b)} -> (left : Vect n a) -> (right : Vect n b) -> ZipVecView xs

export
Eq (ZipVecView xs) where
  _ == _ = True

export
zipVecView : (xs : Vect n (a, b)) -> ZipVecView xs
zipVecView [] = ZVecPair [] []
zipVecView ((l, r)::xs') =
  case zipVecView xs' of
       ZVecPair left right => ZVecPair (l::left) (r::right)
