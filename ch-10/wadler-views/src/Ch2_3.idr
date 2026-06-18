
module Ch2_3

import Data.Nat


%default total
-- 2 Viewing an integer as zero or a succesor

data ViewType = Zero | Succ Int

viewin : Int -> ViewType
viewin n = if n == 0 then Zero
              else if n > 0 then Succ (n - 1)
              else ?undef1

viewout : ViewType -> Int
viewout Zero = 0
viewout (Succ n) = n + 1

partial
export
fib : (m : Int) -> Int
fib m =
  case viewin m of
       Zero => viewout Zero
       (Succ m) => case viewin m of
                        Zero => viewout (Succ (viewout Zero))
                        (Succ n) => fib n + fib (viewout (Succ n))


