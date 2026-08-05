module Main

import Data.List
import Control.Monad.State

import Lib


runTest : Show b => (name : String)
        -> (acc0 : a)
        -> (run : (acc : a) -> b -> Maybe a)
        -> List b -> IO ()
runTest name acc0 run ts =
    let n = length ts
    in  either
          (\err => putStrLn ("Test '" ++ name ++ "' failed with " ++ show err))
          (\_   => putStrLn ("Test '" ++ name ++ "' successful!"))
          $ foldl go (Right acc0) (zip [0..n] ts)
  where
    go : Either (Nat, String) a -> (Nat, b) -> Either (Nat, String) a
    go err@(Left _) _ = err
    go (Right acc) (n, v) =
      case run acc v of
           Nothing => Left (n, show v)
           Just acc' => Right acc'

checkBool : a -> Bool -> Maybe a
checkBool _ False = Nothing
checkBool v True = Just v

testIncrease : List Bool
testIncrease = [ runState 89 (increase 5) == (94, ()) ]

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
            (Node Empty "Sheila" Empty)) "Alice"
            (Node Empty "Bob" (Node Empty "Eve" Empty))

testCountEmpty : List Bool
testCountEmpty =
  [ execState 0 (countEmpty (the (Tree ()) Empty)) == 1
  , execState 0 (countEmpty (Node Empty 1 Empty)) == 2
  , execState 0 (countEmpty testTree) == 7

  , execState 0 (countEmpty2 (the (Tree ()) Empty)) == 1
  , execState 0 (countEmpty2 (Node Empty 1 Empty)) == 2
  , execState 0 (countEmpty2 testTree) == 7
  ]


testCountEmptyNode : List Bool
testCountEmptyNode =
  [ execState (0, 0) (countEmptyNode (the (Tree ()) Empty)) == (1, 0)
  , execState (0, 0) (countEmptyNode (Node Empty 1 Empty)) == (2, 1)
  , execState (0, 0) (countEmptyNode testTree) == (7, 6)

  , execState (0, 0) (countEmptyNode2 (the (Tree ()) Empty)) == (1, 0)
  , execState (0, 0) (countEmptyNode2 (Node Empty 1 Empty)) == (2, 1)
  , execState (0, 0) (countEmptyNode2 testTree) == (7, 6)
  ]
main : IO ()
main = do
  runTest "testIncrease" () checkBool testIncrease
  runTest "testCountEmpty" () checkBool testCountEmpty
  runTest "testCountEmptyNode" () checkBool testCountEmptyNode
