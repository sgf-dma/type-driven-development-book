
module LambdaLifting


-- Lambda lifting example from https://wiki.haskell.org/Lambda_lifting .

-- Lambda lifting technique from "Lambda Lifting: Transforming Programs to
-- Recursive Equations" by T. Johnsson (1985).

-- "Attempt 2" method. Note, the type annotation 'Lazy'. It's required in
-- to avoid evaluation of `f` (which will be recursive call of this function),
-- when not needed.
isqrt'2 : Lazy (Int -> Int) -> Int -> Int -> Int
isqrt'2 f n s =
  if s*s <= n && n < (s+1)*(s+1)
     then s
     else f ((s + (n `div` s)) `div` 2)

-- "Attempt 3" method.
isqrt'3 : Int -> Int -> Int
isqrt'3 n s =
  if s*s <= n && n < (s+1)*(s+1)
     then s
     else isqrt'3 n ((s + (n `div` s)) `div` 2)

isqrt : Int -> Int
isqrt n =
  if n < 0
     then ?a1
     -- No lambda lifting:
     --else isqrt' ((n+1) `div` 2)

     -- Attempt 2 lifting:
     else let g : Int -> Int
              g = isqrt'2 g n
          in g ((n+1) `div` 2)

     -- Attempt 3 lifting:
     --else isqrt'3 n ((n+1) `div` 2)
   where
     isqrt' : Int -> Int
     isqrt' s =
       if s*s <= n && n < (s+1)*(s+1)
          then s
          else isqrt' ((s + (n `div` s)) `div` 2)

-- Exmaples from the paper.
t : Integer
t = let i = 5
     in let f : Integer -> Integer
            f = \x => f (i+i)
         in f (i*i)

-- Or with regular global function (without recursive call).
fExt : Integer -> Integer

tExt : Integer
tExt =
  let i = 5
   in let f : Integer -> Integer
          f = \x => fExt (i+i)
       in f (i*i)

-- Attempt 2.
fL2 : (Integer -> Integer) -> Integer -> Integer -> Integer
fL2 f i x = f (i+i)

t2 : Integer
t2 =
  let i = 5
   in let f : Integer -> Integer
          -- In order to lambda-lift 'f (i+i)', i need to abstract out two
          -- free variables: 'f' and 'i':
          --f = (\f, i, x => f (i+i)) f i
          f = fL2 f i
       in f (i*i)

fL2Ext : Integer -> Integer -> Integer
fL2Ext i x = fExt (i+i)

t2Ext : Integer
t2Ext =
  let i = 5
   in let f : Integer -> Integer
          -- Here function 'fExt' is global, so i need to abstract out only
          -- one free variable 'i'.
          --f = (\i, x => fExt (i+i)) i
          f = fL2Ext i
       in f (i*i)

-- In both these variants type signature of 'f' did not change, only the body
-- of 'f'.

-- Attempt 3.

t3 : Integer
t3 =
  let i = 5
   in let f : Integer -> Integer -> Integer
          -- Here i'm fine with changing 'f' type signature (to preserve
          -- recursion), so i only need to abstract out one free variable 'i'.
          f = (\i, x => f i (i+i))
       in f i (i*i)

fL3 : Integer -> Integer -> Integer
fL3 i x = fL3 i (i+i)

t3' : Integer
t3' = let i = 5 in fL3 i (i*i)

-- But for non-recursive 'Ext' variant nothing changes, it'll be exactly the
-- same!

-- And i may similarly get rid of 'let' altogether and obtain version like `t3'`.
t2Ext' : Integer
t2Ext' = let i = 5 in fL2Ext i (i*i)

-- Therefore, both attempts 2 and 3 results in the same code for non-recursive
-- 'let'. And the difference is only visible, when 'let' binding is recursive.
