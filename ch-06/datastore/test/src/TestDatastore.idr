
module TestDatastore

import Data.String
import Data.Vect

import Schema
import Datastore

exMatchers : List (scm : Schema ** SchemaType scm -> SchemaType scm -> Bool)
exMatchers =
  [(SInt ** (<)), (SString ** isPrefixOf), (SInt .+. SString ** f)]
  where
    f : (Int, String) -> (Int, String) -> Bool
    f (num, str) (x, s) = num == x && str == s

exStore : DataStore
exStore = MkData (((SInt .+. SString) .+. SInt) .+. (SString .+. (SString .+. SInt))) 3
            [ (((1, "abc"), 2), ("d", ("def", 2)))
            , (((1, "abc"), 3), ("e", ("de", 4)))
            , (((3, "def"), 2), ("a", ("abc", 4)))
            ]

export
testStoreSearch : List Bool
testStoreSearch =
  [ searchWith exStore exMatchers SInt 3
        == [ (1, (((1, "abc"), 3), ("e", ("de", 4))))
           , (2, (((3, "def"), 2), ("a", ("abc", 4))))
           ]
  , searchWith exStore exMatchers SInt 4
        == []
  , searchWith exStore exMatchers SString "d"
        == [ (0, (((1, "abc"), 2), ("d", ("def", 2))))
           , (1, (((1, "abc"), 3), ("e", ("de", 4))))
           , (2, (((3, "def"), 2), ("a", ("abc", 4))))
           ]
  , searchWith exStore exMatchers SString "def"
        == [ (0, (((1, "abc"), 2), ("d", ("def", 2))))
           , (2, (((3, "def"), 2), ("a", ("abc", 4))))
           ]
  , searchWith exStore exMatchers SString "x"
        == []

  -- 5-6
  , searchWith exStore exMatchers (SInt .+. SString) (1, "abc")
        == [ (0, (((1, "abc"), 2), ("d", ("def", 2))))
           , (1, (((1, "abc"), 3), ("e", ("de", 4))))
           ]
  , searchWith exStore exMatchers (SInt .+. SString) (1, "bc")
        == []

  -- 7-10
  , searchWith exStore exMatchers (SString .+. SInt) ("d", 1)
        == [ (0, (((1, "abc"), 2), ("d", ("def", 2))))
           , (1, (((1, "abc"), 3), ("e", ("de", 4))))
           ]
  , searchWith exStore exMatchers (SString .+. SInt) ("d", 3)
        == [ (1, (((1, "abc"), 3), ("e", ("de", 4)))) ]
  , searchWith exStore exMatchers (SString .+. SInt) ("e", 3)
        == []
  , searchWith exStore exMatchers (SString .+. SInt) ("d", 4)
        == []

  -- 11-12
  , searchWith exStore exMatchers (SString .+. (SString .+. SInt)) ("d", ("d", 1))
        == [ (0, (((1, "abc"), 2), ("d", ("def", 2)))) ]
  , searchWith exStore exMatchers ((SInt .+. SString) .+. SInt) ((1, "abc"), 1)
        == [ (0, (((1, "abc"), 2), ("d", ("def", 2))))
           , (1, (((1, "abc"), 3), ("e", ("de", 4))))
           ]

  -- 13-
  , searchWith exStore [] (SInt .+. SString) (1, "b")
        == [ (0, (((1, "abc"), 2), ("d", ("def", 2))))
           , (1, (((1, "abc"), 3), ("e", ("de", 4))))
           ]
  , searchWith exStore [] (SString .+. SInt) ("d", 4)
        == [ (1, (((1, "abc"), 3), ("e", ("de", 4)))) ]
  ]

