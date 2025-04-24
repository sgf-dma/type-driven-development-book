
module TestSchema

import Data.List
import Data.Vect

import Utils
import Schema

tScm1 : Schema
tScm1 = (((SInt .+. SString) .+. SInt) .+. (SInt .+. SString))

tVal1 : SchemaType (((SInt .+. SString) .+. SInt) .+. (SInt .+. SString))
tVal1 = (((2, "a"), 3), (4, "b"))

data Res = MkRes (Nat, Schema)

Eq Res where
  MkRes (x, scm1) == MkRes (y, scm2) = x == y && (scm1 `eqSchema` scm2)

Ord Res where
  MkRes (x, scm1) < MkRes (y, scm2) = x < y

tRes1 : List Res
tRes1 =
  [ MkRes (0, SInt)
  , MkRes (0, SString)
  , MkRes (0, SInt)
  , MkRes (0, SInt)
  , MkRes (0, SString)

  , MkRes (1, SInt .+. SString)
  , MkRes (1, SInt .+. SString)

  , MkRes (2, ((SInt .+. SString) .+. SInt))

  , MkRes (3, (((SInt .+. SString) .+. SInt) .+. (SInt .+. SString)))
  ]

sortRes : List (Nat, Schema) -> List (Nat, Schema)

vectToRes : (n ** Vect n (List Schema)) -> List Res
vectToRes (_ ** vs) = foldr go (const []) vs 0
  where
    go : List Schema -> (Nat -> List Res) -> Nat -> List Res
    go xs acc i = map (\s => MkRes (i, s)) xs ++ acc (i + 1)

export
testAllSubtrees : List Bool
testAllSubtrees =
  [ cmpWith tRes1 . map MkRes $ allSubtrees tScm1 []
  , cmpWith tRes1 . map MkRes . snd $ allSubtrees' tScm1 []
  , cmpWith tRes1 . vectToRes . snd $ allSubtrees2 tScm1 (_ ** [])
  ]
  where
    cmpWith : List Res -> List Res -> Bool
    cmpWith res = all (uncurry (==)) . zip res . sort

export
testSubtrees : List Bool
testSubtrees =
  [ findSubtreeValues tScm1 SInt tVal1 == [2, 3, 4]
  , findSubtreeValues tScm1 SString tVal1 == ["a", "b"]
  , findSubtreeValues tScm1 (SInt .+. SString) tVal1 == [(2, "a"), (4, "b")]
  , findSubtreeValues tScm1 (SString .+. SInt) tVal1 == []
  , findSubtreeValues tScm1 ((SInt .+. SString) .+. SInt) tVal1 == [((2, "a"), 3)]
  , findSubtreeValues tScm1 tScm1 tVal1 == [tVal1]

  , findSubtreeValuesV tScm1 SInt tVal1 == [2, 3, 4]
  , findSubtreeValuesV tScm1 SString tVal1 == ["a", "b"]
  , findSubtreeValuesV tScm1 (SInt .+. SString) tVal1 == [(2, "a"), (4, "b")]
  , findSubtreeValuesV tScm1 (SString .+. SInt) tVal1 == []
  , findSubtreeValuesV tScm1 ((SInt .+. SString) .+. SInt) tVal1 == [((2, "a"), 3)]
  , findSubtreeValuesV tScm1 tScm1 tVal1 == [tVal1]
  ]
