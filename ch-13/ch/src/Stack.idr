module Stack

import Data.Vect

%default total

data StackCmd : Type -> Type -> Nat -> Nat -> Type where
  Push : ty -> StackCmd ty () n (S n)
  Pop : StackCmd ty ty (S n) n
  Top : StackCmd ty ty (S n) (S n)

  Pure : a -> StackCmd ty a n n
  (>>=) : StackCmd ty a n1 n2 -> (a -> StackCmd ty b n2 n3) -> StackCmd ty b n1 n3

(>>) : StackCmd ty () n1 n2 -> StackCmd ty b n2 n3 -> StackCmd ty b n1 n3
mx >> my = mx >>= \_ => my

testAdd : StackCmd Integer Integer 1 2
--testAdd : StackCmd Integer String 0 1
testAdd = do
  Push 10
  Push 20
  Push 30
  val1 <- Pop
  val2 <- Pop
  Pure (val1 + val2)
  --Pure (show (val1 + val2))

run : Vect n1 ty -> StackCmd ty c n1 n2 -> (c, Vect n2 ty)
run xs0 (Push x) = ((), x::xs0)
run (x::xs0) Pop = (x, xs0)
run (x::xs0) Top = (x, x::xs0)
run xs0 (Pure y) = (y, xs0)
run xs0 (mx >>= f) = let (z, xs1) = run xs0 mx in run xs1 (f z)

doAdd : StackCmd Integer () (S (S height)) (S height)
doAdd = do
  val1 <- Pop
  val2 <- Pop
  Push (val1 + val2)

-- This is esentially the same as `StackCmd`, but actions are running in IO.
-- It may be easily merged with `StackCmd`, but it can _not_ be merged into
-- `StackIO` (see below why).
-- I don't have Bind here, because i'll use `StackIO`'s Do instead.
data StackCmdIO : Type -> Type -> Nat -> Nat -> Type where
  GetStr : StackCmdIO ty String s s
  PutStr : String -> StackCmdIO ty () s s
  SCmd : StackCmd ty a n1 n2 -> StackCmdIO ty a n1 n2

runCmdIO : Vect n1 ty -> StackCmdIO ty a n1 n2 -> IO (a, Vect n2 ty)
runCmdIO xs0 GetStr = do
  putStr "> "
  inp <- getLine
  pure (inp, xs0)
runCmdIO xs0 (PutStr s) = do
  putStrLn s
  pure ((), xs0)
runCmdIO xs0 (SCmd cmd) = pure (run xs0 cmd)

data StackIO : Type -> Nat -> Type where
  -- If i add 'StackCmdIO' constructors here, 'StackIO' would no longer be
  -- infinite data type, i.e. i would be able to construct finite values. And
  -- then i'll need more type parameters to be able to evaluate it. But if
  -- 'StackIO' is infinite, resulting value and 'Inf' value's type parameters
  -- does not matter, because these values would never be computed and i may
  -- use theirs type parameters as i like.
  -- I need an element type and (initial) state in `StackIO` type for helping
  -- with type inference.
  Do : StackCmdIO ty a n1 n2 -> (a -> Inf (StackIO ty n2)) -> StackIO ty n1

data Fuel : Type where
  Dry : Fuel
  More : Lazy Fuel -> Fuel

partial
forever : Fuel
forever = More forever

runIO : Fuel -> Vect n1 ty -> StackIO ty n1 -> IO ()
runIO Dry xs0 (Do mx _) = do
  _ <- runCmdIO xs0 mx
  pure ()
runIO (More fuel) xs0 (Do mx f) = do
  (z, xs1) <- runCmdIO xs0 mx
  runIO fuel xs1 (f z)

namespace StackIO
  export
  (>>=) : StackCmdIO ty a n1 n2 -> (a -> Inf (StackIO ty n2)) -> StackIO ty n1
  (>>=) = Do
  export
  (>>) : StackCmdIO ty a n1 n2 -> Inf (StackIO ty n2) -> StackIO ty n1
  mx >> my = mx >>= (\_ => my)
