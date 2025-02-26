
module Main

import Datastore
import Cmd
import Data.Vect
import System.REPL

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
