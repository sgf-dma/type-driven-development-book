module Main

import Data.List

import Lib


testShape : List Bool
testShape =
  [ Circle 4 == Circle 4
  , Circle 4 /= Circle 5
  , Triangle 3 3 == Triangle 3 3
  , Rectangle 2 4 /= Rectangle 5 6

  , sort [Circle 3, Triangle 3 9, Rectangle 2 6, Circle 4, Rectangle 2 7]
    == [Rectangle 2 6, Triangle 3 9, Rectangle 2 7, Circle 3, Circle 4]
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
  runTest "testShape" () checkBool testShape
