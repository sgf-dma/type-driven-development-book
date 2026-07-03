module Main

import Data.Fin
import Data.List

import Lib


testArithInputs : List Bool
testArithInputs =
  [ (map finToNat . take 10 $ arithInputs1 (-1) [0..])
      == [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  , (map finToNat . take 10 $ arithInputs1 0 [0..])
      == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  , (map finToNat . take 10 $ arithInputs1 1 [0..])
      == [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  , (map finToNat . take 10 $ arithInputs1 2 [0..])
      == [1, 2, 1, 2, 1, 2, 1, 2, 1, 2]
  , (map finToNat . take 10 $ arithInputs1 3 [0..])
      == [1, 2, 3, 1, 2, 3, 1, 2, 3, 1]
  , (map finToNat . take 10 $ arithInputs1 4 [0..])
      == [1, 2, 3, 4, 1, 2, 3, 4, 1, 2]

  -- 6
  , (map finToNat . take 10 $ arithInputs1 5 [0..])
      == [1, 2, 3, 4, 5, 1, 2, 3, 4, 5]
  , (map finToNat . take 10 $ arithInputs1 6 [0..])
      == [1, 2, 3, 4, 5, 6, 1, 2, 3, 4]
  , (map finToNat . take 10 $ arithInputs1 7 [0..])
      == [1, 2, 3, 4, 5, 6, 7, 1, 2, 3]
  , (map finToNat . take 10 $ arithInputs1 8 [0..])
      == [1, 2, 3, 4, 5, 6, 7, 8, 1, 2]
  , (map finToNat . take 10 $ arithInputs1 9 [0..])
      == [1, 2, 3, 4, 5, 6, 7, 8, 9, 1]

  -- 11
  , (map finToNat . take 10 $ arithInputs1 10 [0..])
      == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  , (map finToNat . take 10 $ arithInputs1 11 [0..])
      == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

  -- Version with zeros.
  -- 13
  , (map finToNat . take 10 $ arithInputs2 (-1) [0..])
      == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  , (map finToNat . take 10 $ arithInputs2 0 [0..])
      == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  , (map finToNat . take 10 $ arithInputs2 1 [0..])
      == [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
  , (map finToNat . take 10 $ arithInputs2 2 [0..])
      == [0, 1, 2, 0, 1, 2, 0, 1, 2, 0]
  , (map finToNat . take 10 $ arithInputs2 3 [0..])
      == [0, 1, 2, 3, 0, 1, 2, 3, 0, 1]
  , (map finToNat . take 10 $ arithInputs2 4 [0..])
      == [0, 1, 2, 3, 4, 0, 1, 2, 3, 4]

  , (map finToNat . take 10 $ arithInputs2 5 [0..])
      == [0, 1, 2, 3, 4, 5, 0, 1, 2, 3]
  , (map finToNat . take 10 $ arithInputs2 6 [0..])
      == [0, 1, 2, 3, 4, 5, 6, 0, 1, 2]
  , (map finToNat . take 10 $ arithInputs2 7 [0..])
      == [0, 1, 2, 3, 4, 5, 6, 7, 0, 1]
  , (map finToNat . take 10 $ arithInputs2 8 [0..])
      == [0, 1, 2, 3, 4, 5, 6, 7, 8, 0]
  , (map finToNat . take 10 $ arithInputs2 9 [0..])
      == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

  , (map finToNat . take 10 $ arithInputs2 10 [0..])
      == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  , (map finToNat . take 10 $ arithInputs2 11 [0..])
      == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

  -- Nat version.
  , (map finToNat . take 10 $ arithInputs2 0 [0..])
      == (map finToNat . take 10 $ arithInputs3 0 [0..])
  , (map finToNat . take 10 $ arithInputs2 1 [0..])
      == (map finToNat . take 10 $ arithInputs3 1 [0..])
  , (map finToNat . take 10 $ arithInputs2 2 [0..])
      == (map finToNat . take 10 $ arithInputs3 2 [0..])
  , (map finToNat . take 10 $ arithInputs2 3 [0..])
      == (map finToNat . take 10 $ arithInputs3 3 [0..])
  , (map finToNat . take 10 $ arithInputs2 4 [0..])
      == (map finToNat . take 10 $ arithInputs3 4 [0..])

  , (map finToNat . take 10 $ arithInputs2 5 [0..])
      == (map finToNat . take 10 $ arithInputs3 5 [0..])
  , (map finToNat . take 10 $ arithInputs2 6 [0..])
      == (map finToNat . take 10 $ arithInputs3 6 [0..])
  , (map finToNat . take 10 $ arithInputs2 7 [0..])
      == (map finToNat . take 10 $ arithInputs3 7 [0..])
  , (map finToNat . take 10 $ arithInputs2 8 [0..])
      == (map finToNat . take 10 $ arithInputs3 8 [0..])
  , (map finToNat . take 10 $ arithInputs2 9 [0..])
      == (map finToNat . take 10 $ arithInputs3 9 [0..])

  , (map finToNat . take 10 $ arithInputs2 10 [0..])
      == (map finToNat . take 10 $ arithInputs3 10 [0..])
  , (map finToNat . take 10 $ arithInputs2 11 [0..])
      == (map finToNat . take 10 $ arithInputs3 11 [0..])
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
  runTest "testArithInputs" () checkBool testArithInputs
