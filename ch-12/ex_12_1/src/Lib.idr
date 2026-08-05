module Lib

import Control.Monad.State

-- Ex. 1
update : (stateTy -> stateTy) -> State stateTy ()
update f = get >>= put . f

export
increase : Nat -> State Nat ()
increase n = update (+n)

-- Ex. 2
public export
data Tree a = Empty
            | Node (Tree a) a (Tree a)

flatten : Tree a -> List a
flatten Empty = []
flatten (Node left val right) = flatten left ++ val :: flatten right

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
            (Node Empty "Sheila" Empty)) "Alice"
            (Node Empty "Bob" (Node Empty "Eve" Empty))

export
countEmpty : Tree a -> State Nat ()
countEmpty Empty = update (+1)
countEmpty (Node left _ right) = countEmpty left >> countEmpty right

traverse : Monad m => (f : Maybe a -> m ()) -> Tree a -> m ()
traverse f Empty = f Nothing
traverse f (Node left val right) = do
  traverse f left
  f (Just val)
  traverse f right

export
countEmpty2 : Tree a -> State Nat ()
countEmpty2 = traverse $ \mval => case mval of
                                       Nothing => update (+1)
                                       _ => pure ()

-- Ex. 3
export
countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = update (\(e, n) => (e+1, n))
countEmptyNode (Node left _ right) = do
  countEmptyNode left
  update (\(e, n) => (e, n+1))
  countEmptyNode right

export
countEmptyNode2 : Tree a -> State (Nat, Nat) ()
countEmptyNode2 = traverse $ \mval => case mval of
                                 Nothing => update (\(e, n) => (e+1, n))
                                 Just _  => update (\(e, n) => (e  , n+1))
