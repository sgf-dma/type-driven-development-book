module Main

import Data.List

import Lib

testExpr : List Bool
testExpr =
  [ show (the (Expr Int) (6 + 3 * 12)) == "V6 + V3 * V12"
  , show (the (Expr Int) ((6 + 3) * 12)) == "(V6 + V3) * V12"
  , show (the (Expr Int) (6 * 3 + 12)) == "V6 * V3 + V12"

  , show (the (Expr Int) ((abs (5 `div` 3)) + 1) * 2) == "(abs(V5 `div` V3) + V1) * V2"
  , show (the (Expr Int) (abs (5 `div` 3) + 1)) == "abs(V5 `div` V3) + V1"
  , show (the (Expr Int) (5 `div` 3)) == "V5 `div` V3"
  , show (the (Expr Int) ((5 `div` 3 + 3 * 2))) == "(V5 `div` V3) + V3 * V2"

  , the (Expr Int) (2 + 4) == 3 + 3
  , the (Expr Int) (2 + 4) /= 3 + 4

  , let x : Expr Integer = 6 * 3 + 12 in the Integer (cast x) == 30

  , map (*2) (the (Expr _) (1 + 2 * 3)) == Add (Val 2) (Mul (Val 4) (Val 6))
  , show (map show (the (Expr Int) (1 + 2 * 3)))
        == show (Add (Val "1") (Mul (Val "2") (Val "3")))

  , foldr (+) 0 (the (Vect _ _) [1,2,3,4,5]) == 15
  , the (Vect _ _) [1,2,3,4] == [1,2,3,4]
  , the (Vect _ _) [1,2,3,4] /= [5,6,7,8]
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
  runTest "testExpr" () checkBool testExpr
