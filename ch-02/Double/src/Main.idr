module Main

double : (val : Int) -> Int
double x = x + x

add : Int -> Int -> Int
add x y = x + y

main : IO ()
main = putStrLn "Hello from Idris2!"
