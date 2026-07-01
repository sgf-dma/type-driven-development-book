module Lib

import Data.Stream
import Data.List
import Data.Primitives.Views

-- %auto_lazy off

test : String
test = "Hello from Idris2!"

countFrom : Integer -> List Integer
countFrom n = n :: countFrom (n + 1)

data InfList : Type -> Type where
  (::) : (val : a) -> Inf (InfList a) -> InfList a

total
countFrom2 : Integer -> InfList Integer
--countFrom2 n = n :: Delay (countFrom2 (n + 1))
countFrom2 n = n :: countFrom2 (n + 1)

total
getPrefix : (count : Nat) -> InfList a -> List a
getPrefix Z _ = []
--getPrefix (S k) (v::infvs) = v :: getPrefix k (Force infvs)
getPrefix (S k) (v::infvs) = v :: getPrefix k infvs

total
labelWith : (labels : Stream a) -> (values : List b) -> List (a, b)
labelWith _ [] = []
labelWith (l::ls) (v::vs) = (l, v) :: labelWith ls vs

total
label : List b -> List (Nat, b)
label = labelWith (iterate (+1) 0)
