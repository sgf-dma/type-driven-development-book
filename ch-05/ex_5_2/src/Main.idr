
module Main

import Lib

replWith' : a -> String -> (a -> String -> Maybe (String, a)) -> IO ()
replWith' s0 prompt f = do
  putStr prompt
  str <- getLine
  case f s0 str of
       Nothing => pure ()
       Just (reply, s') => putStr reply >> replWith' s' prompt f

repl' : String -> (String -> String) -> IO ()
repl' prompt f = replWith' () prompt (\s, str => Just (f str, s))

main : IO ()
main = do
  chooseNumber >>= guess2
