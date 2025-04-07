
module Main

import Datastore
import Cmd
import Data.Vect
import System.REPL

main : IO ()
main = replWith (MkData (SString .+. SString .+. SInt) _ []) "Command: " processInput
