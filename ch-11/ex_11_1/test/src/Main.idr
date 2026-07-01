module Main

import Data.List

import Lib


testEx1 : List Bool
testEx1 = [ take 5 (every_other [1..]) == [2, 4, 6, 8, 10] ]

testEx2 : List Bool
testEx2 =
  [ getPrefix 10 (map (*2) (countFrom 1)) == [2, 4, 6, 8, 10, 12, 14, 16, 18, 20] ]

testEx3 : List Bool
testEx3 = [ coinFlips 4 [1..] == [Tails, Heads, Tails, Heads] ]

testEx4 : List Bool
testEx4 = [ take 3 (square_root_approx 10 10) == [10.0, 5.5, 3.659090909090909]
          , take 3 (square_root_approx 100 25) == [25.0, 14.5, 10.698275862068964]
          ]

testEx5 : List Bool
testEx5 = [ square_root 6 == 2.449489742783178
          , square_root 2500 == 50.0
          , square_root 2501 == 50.009999000199954
          ]

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

main : IO ()
main = do
  runTest "testEx1" () checkBool testEx1
  runTest "testEx2" () checkBool testEx2
  runTest "testEx3" () checkBool testEx3
  runTest "testEx4" () checkBool testEx4
  runTest "testEx5" () checkBool testEx5
