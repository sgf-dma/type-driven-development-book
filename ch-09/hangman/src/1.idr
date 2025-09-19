
import Data.Maybe
import Decidable.Equality
import Data.List
import Data.List.Elem

data D : List a -> Type where
  Mk1 : {xs : List a} -> D xs
  Mk2 : {xs : List a} -> D xs

g : {xs : List a} -> D xs -> Elem z xs -> Int
g Mk1 _ = ?w1
g {xs = []} (Mk2) Here impossible
g {xs = []} (Mk2) (There _) impossible
g {xs = _::xs} (Mk2 {xs = .(_)}) Here = ?w3
g {xs = _::xs} (Mk2) (There _) = ?w5

0 foo : (x : Maybe a) -> IsJust x -> a
foo .(Just x) ItIsJust = x

0 bar : (x : Maybe a) -> IsJust x -> a
bar (Just x) ItIsJust = x
