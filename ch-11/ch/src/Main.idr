
import Lib

import System

%default total

partial
main : IO ()
main = do
  -- Fast version using 'Integer':
  runFuel foreverFuel (quiz2Inf 0 (arithInputs2 5 (randoms 1)))
  -- Very slow version using 'Nat':
  --runFuel foreverFuel (quiz2Inf 0 (arithInputs3 5 (randomNats 1)))
