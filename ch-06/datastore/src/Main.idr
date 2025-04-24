
module Main

import Schema
import Datastore
import Cmd
import Datastore2
import Cmd2
import Data.Vect
import System.REPL

main : IO ()
main = replWith (MkData (SString .+. SString .+. SInt) _ []) "Command: " processInput

main2 : IO ()
main2 = replWith initStore2 "Command: " processInput2
  where
    initStore2 : (scm : Schema ** DataStore2 scm)
    initStore2 = (SString .+. SString .+. SInt ** MkData2 _ [])
