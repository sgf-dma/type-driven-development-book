module Lib

import System.File.Handle
import System.File.ReadWrite
import Data.String
import Data.Vect

readToBlank : IO (List String)
--readToBlank = go id >>= \zs => pure (zs [])
readToBlank = go id <*> pure []
  where
    go : (List String -> List String) -> IO (List String -> List String)
    go zs = do
      str <- getLine
      if str == ""
         then pure zs
         else go (zs . (str ::))

readAndSave : IO ()
readAndSave = do
  putStrLn "Enter file content:"
  cnt <- readToBlank
  putStrLn "Enter filename:"
  fn <- getLine
  Right _ <- writeFile fn (unlines cnt)
    | Left err => putStrLn ("Error: " ++ show err)
  putStrLn "successfully written"
  pure ()

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile fn = do
    Right h <- openFile fn Read
      | Left err => putStrLn ("Error: " ++ show err) >> pure (0 ** [])
    res <- go h (0 ** [])
    closeFile h
    pure res
  where
    go : File -> (n ** Vect n String) -> IO (n ** Vect n String)
    go h z@(n ** zs) = do
      Right cnt <- fGetLine h
        | Left err => putStrLn ("Error: " ++ show err) >> pure z
      if cnt == ""
         then pure z
         else go h (S n ** zs `snoc` trim cnt)

