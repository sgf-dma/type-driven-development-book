
module TestSchema

import Data.List
import Data.Vect
import Data.String

import Utils
import Schema

export
testSchemaDisplay : List Bool
testSchemaDisplay =
  [ matchSchema SInt
  , matchSchema (SInt .+. SString)
  , matchSchema ((SInt .+. SString) .+. SString)
  , matchSchema (SInt .+. (SString .+. SInt))
  , matchSchema ((SInt .+. SString) .+. (SString .+. SInt))
  , matchSchema (((SInt .+. SString) .+. SInt) .+. (SString .+. (SString .+. SInt)))
  ]
  where
    matchSchema : Schema -> Bool
    matchSchema scm = fromMaybe False $ do
      let d = displaySchema False scm
          d' = displaySchema True scm
      (scmRes,  "") <- parseSchemaPrefix d  | _ => Nothing
      (scmRes', "") <- parseSchemaPrefix d' | _ => Nothing
      pure (scmRes == scmRes' && scmRes == scm)

export
testSchemaParse : List Bool
testSchemaParse =
  [ parseSchemaPrefix "Int" == Just (SInt, "")

  -- 1-3
  , parseSchemaPrefix "  Int" == Just (SInt, "")
  , parseSchemaPrefix "Int  " == Just (SInt, "  ")
  , parseSchemaPrefix "  Int  " == Just (SInt, "  ")

  -- 4-8
  , parseSchemaPrefix "(Int)" == Just (SInt, "")
  , parseSchemaPrefix "(  Int)" == Just (SInt, "")
  , parseSchemaPrefix "(Int  )" == Just (SInt, "")
  , parseSchemaPrefix "(  Int  )" == Just (SInt, "")
  , parseSchemaPrefix "  (  Int  )  " == Just (SInt, "  ")

  -- 9-13
  , parseSchemaPrefix "Int  String" == Just (SInt .+. SString, "")
  , parseSchemaPrefix "Int  (String)" == Just (SInt .+. SString, "")
  , parseSchemaPrefix "  ( (Int)  (String  ) )" == Just (SInt .+. SString, "")
  , parseSchemaPrefix "  ( (  Int)  (  String) )Test" == Just (SInt .+. SString, "Test")
  , parseSchemaPrefix "  ( (  (Int)  )  ((  String) ))(Test)" == Just (SInt .+. SString, "(Test)")

  -- 14-
  , parseSchemaPrefix "((Int  String) Int) (String String Int)"
      == Just (((SInt .+. SString) .+. SInt) .+. (SString .+. (SString .+. SInt)), "")
  ]

export
testSchemaValue : List Bool
testSchemaValue =
  [ parsePrefix False SInt "2" == Just (2, "")
  , parsePrefix False SInt "  2" == Just (2, "")
  , parsePrefix False SInt "2  " == Just (2, "  ")
  , parsePrefix False SInt "  2  " == Just (2, "  ")
  , parsePrefix True SInt "  (2)  " == Just (2, "  ")
  , parsePrefix False SInt "( (2 ))  " == Just (2, "  ")
  , parsePrefix True SInt "( (( 2) ))  " == Just (2, "  ")
  , parsePrefix True SInt "(( ( 2 )  ))  " == Just (2, "  ")

  -- 8-11
  , parsePrefix False (SInt .+. SString) "  2  ( (\"a b c\" ))  " == Just ((2, "a b c"), "  ")
  , parsePrefix True ((SInt .+. SString) .+. SString) " ( ( 2   \"a b c\")  \" d \")"
      == Just (((2, "a b c"), " d "), "")
  , parsePrefix False (SInt .+. (SString .+. SString)) "  2   (\"a b c\")  \" d \""
      == Just ((2, ("a b c", " d ")), "")
  , parsePrefix False ((SInt .+. SString) .+. (SString .+. SInt)) "  ((2   \"a b c\")  ((\" d \" 44) )) 55"
      == Just (((2, "a b c"), (" d ", 44)), " 55")

  -- 12-
  , parsePrefix False (((SInt .+. SString) .+. SInt) .+. (SString .+. (SString .+. SInt))) "((  (2 \" a \") 3) ) (\"b\"   (\"c  \")  ( (4)))  "
      == Just ((((2, " a "), 3), ("b", ("c  ", 4))), "  ")
  ]

tScm1 : Schema
tScm1 = (((SInt .+. SString) .+. SInt) .+. (SInt .+. SString))

tVal1 : SchemaType (((SInt .+. SString) .+. SInt) .+. (SInt .+. SString))
tVal1 = (((2, "a"), 3), (4, "b"))

data Res = MkRes (Nat, Schema)

Eq Res where
  MkRes (x, scm1) == MkRes (y, scm2) = x == y && (scm1 == scm2)

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

vectToRes : (n ** Vect n (List Schema)) -> List Res
vectToRes (_ ** vs) = foldr go (const []) vs 0
  where
    go : List Schema -> (Nat -> List Res) -> Nat -> List Res
    go xs acc i = map (\s => MkRes (i, s)) xs ++ acc (i + 1)

export
testSchemaSubtreesAll : List Bool
testSchemaSubtreesAll =
  [ cmpWith tRes1 . map MkRes $ allSubtrees tScm1 []
  , cmpWith tRes1 . map MkRes . snd $ allSubtrees' tScm1 []
  , cmpWith tRes1 . vectToRes . snd $ allSubtrees2 tScm1 (_ ** [])
  ]
  where
    cmpWith : List Res -> List Res -> Bool
    cmpWith res = all (uncurry (==)) . zip res . sort

export
testSchemaSubtrees : List Bool
testSchemaSubtrees =
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

exMatchers : List (scm : Schema ** SchemaType scm -> SchemaType scm -> Bool)
exMatchers =
  [(SInt ** (<)), (SString ** isPrefixOf), (SInt .+. SString ** f)]
  where
    f : (Int, String) -> (Int, String) -> Bool
    f (num, str) (x, s) = num == x && str == s

export
testSchemaMatcher : List Bool
testSchemaMatcher =
  [ buildMatcher SInt 1 exMatchers 2
  , buildMatcher SInt 2 exMatchers 1 == False
  , buildMatcher SString "a" exMatchers "abc"
  , buildMatcher SString "b" exMatchers "abc" == False

  -- 4-6
  , buildMatcher (SInt .+. SString) (1, "abc") exMatchers (1, "abc")
  , buildMatcher (SInt .+. SString) (1, "abc") exMatchers (2, "abc") == False
  , buildMatcher (SInt .+. SString) (1, "a") exMatchers (2, "abc") == False

  -- 7-10
  , buildMatcher (SString .+. SInt) ("a", 1) exMatchers ("abc", 2)
  , buildMatcher (SString .+. SInt) ("a", 2) exMatchers ("abc", 1) == False
  , buildMatcher (SString .+. SInt) ("b", 1) exMatchers ("abc", 2) == False
  , buildMatcher (SString .+. SInt) ("abc", 1) exMatchers ("abc", 1) == False

  -- 11-12
  , buildMatcher (SInt .+. (SInt .+. SString)) (3, (1, "abc")) exMatchers (4, (1, "abc"))
  , buildMatcher (SInt .+. (SInt .+. SString)) (4, (1, "abc")) exMatchers (3, (1, "abc")) == False

  -- 11-14
  , buildMatcher ((SString .+. SInt) .+. (SInt .+. SString)) (("a", 3), (1, "abc"))
      exMatchers (("abc", 4), (1, "abc"))
  , buildMatcher ((SString .+. SInt) .+. (SInt .+. SString)) (("a", 4), (1, "abc"))
      exMatchers (("abc", 3), (1, "abc")) == False
  , buildMatcher ((SString .+. SInt) .+. (SInt .+. SString)) (("b", 3), (1, "abc"))
      exMatchers (("abc", 4), (1, "abc")) == False
  , buildMatcher ((SString .+. SInt) .+. (SInt .+. SString)) (("abc", 3), (1, "abc"))
      exMatchers (("abc", 3), (1, "abc")) == False

  -- 15-18
  , buildMatcher ((SString .+. SInt) .+. (SInt .+. SString)) (("a", 3), (1, "abc"))
      [] (("abc", 3), (1, "abc"))
  , buildMatcher ((SString .+. SInt) .+. (SInt .+. SString)) (("c", 3), (1, "b"))
      [] (("abc", 3), (1, "abc"))
  , buildMatcher ((SString .+. SInt) .+. (SInt .+. SString)) (("a", 4), (1, "abc"))
      [] (("abc", 3), (1, "abc")) == False
  , buildMatcher ((SString .+. SInt) .+. (SInt .+. SString)) (("d", 3), (1, "c"))
      [] (("abc", 3), (1, "abc")) == False
  ]

