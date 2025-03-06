module Lib

printLonger : IO ()
printLonger = do
  putStr "Input string 1: "
  str1 <- getLine
  putStr "Input string 2: "
  str2 <- getLine
  let l1 = length str1
      l2 = length str2
  putStrLn . show $ if l1 > l2 then l1 else l2

printLonger' : IO ()
printLonger' =
  putStr "Input string 1: " >>= \_ =>
  getLine >>= \str1 =>
  putStr "Input string 2: " >>= \_ =>
  getLine >>= \str2 =>
    let l1 = length str1
        l2 = length str2
    in  putStrLn . show $ if l1 > l2 then l1 else l2

test : String
test = "Hello from Idris2!"
