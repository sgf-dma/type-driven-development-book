module Lib

import Data.Vect
import Data.String
import Data.List

Position : Type
Position = (Double, Double)

Polygon : Nat -> Type
Polygon n = Vect n Position

tri : Polygon 3
tri = [(0, 0), (1, 1), (2, 2)]

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int

getStringOrInt : (b : Bool) -> StringOrInt b
getStringOrInt False = "Ninety four"
getStringOrInt True = 94

valToString : (b : Bool) -> StringOrInt b -> String
valToString False str = trim str
valToString True n = cast n

valToString2 : (b : Bool) -> (case b of
                                  False => String
                                  True  => Int) -> String
valToString2 False y = trim y
valToString2 True y = cast y

valToString3 : {t : Type} -> t -> String
valToString3 {t = Int} y = show y
valToString3 {t = String} y = trim y
valToString3 {t = _} _ = "Not implemented"

typeRep : Type -> String

searchTy : List Type -> Type -> Maybe Type
--searchTy ts t0 = case findIndex (\t => typeRep t0 == typeRep t) ts of
--                     Nothing => Nothing
--                     Just i => let y = index' ts i in Just y
searchTy ts t0 = index' ts <$> findIndex (\t => typeRep t0 == typeRep t) ts

{-
partial searchTy : Show a => List a -> a -> Maybe a
searchTy ts t0 = case findIndex (\t => show t0 == show t) ts of
                     Nothing => Nothing
                     Just i => let y = index' ts i in ?c --Just (index i ts)
                     -}

valToString4 : {t : Type} -> t -> String
--valToString4 y = ?c1 --show y
--valToString4 _ = ?c3 --"Not implemented"

AdderType : Nat -> Type
AdderType Z = Int
AdderType (S n) = (y : Int) -> AdderType n

myAdder : (n : Nat) -> AdderType n
myAdder = go []
  where
    go : List Int -> (n : Nat) -> AdderType n
    go zs Z = sum zs
    go zs (S n) = \y => go (y :: zs) n

adder : (n : Nat) -> Int -> AdderType n
adder Z acc = acc
adder (S n) acc = \y => adder n (y + acc)

AdderType' : Nat -> (a : Type) -> Type
AdderType' Z a = a
AdderType' (S n) a = a -> AdderType' n a

adder' : Num a => (n : Nat) -> a -> AdderType' n a
adder' Z acc = acc
adder' (S n) acc = \y => adder' n (y + acc)

{-
showType : Type -> String
showType Int = "Int"
showType (Nat -> b) = ?c2
showType _ = "None"
-}
