module Lib

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

-- See ../ch/src/Stack.idr for explanation of such definition.
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

data StkInput = Number Integer | Add | Sub | Mul | Neg | Dsc | Dup

strToInput : String -> Either String StkInput
strToInput "add" = Right Add
strToInput "sub" = Right Sub
strToInput "mul" = Right Mul
strToInput "neg" = Right Neg
strToInput "dsc" = Right Dsc
strToInput "dup" = Right Dup
strToInput "0" = Right (Number 0)
strToInput xstr =
  let x = the Integer (cast xstr)
  in  if x == 0
        then Left "Wrong command or number"
        else Right (Number x)

doNeg : StackCmd Integer () (S n) (S n)
doNeg = do
  x <- Pop
  Push (-x)

doMul : StackCmd Integer () (S (S n)) (S n)
doMul = do
  x <- Pop
  y <- Pop
  Push (x*y)

mutual
  -- Note, that i can't sequence `StackCmdIO` actions, only `StackIO`.
  -- Therefore, i need to recurse to `calc` here.
  showTop : {n : Nat} -> StackIO Integer (S n)
  showTop = do
    x <- SCmd Top
    PutStr (show x)
    calc

  add : {n : Nat} -> StackIO Integer n
  add {n = S (S n')} = do
    --x <- SCmd Pop
    --y <- SCmd Pop
    --SCmd (Push (x+y))
    SCmd doAdd
    -- I can't write
    --
    --      showTop
    --      calc
    --
    -- here and need to recurse into `calc` in nested function call
    -- (`showTop`), because i can't sequence `StackCmdIO` actions.
    showTop
    --result <- SCmd Top
    --PutStr (show result)
    --calc
  add = do
    PutStr "Fewer than two items on stack"
    calc

  -- Ex 2.
  neg : {n : Nat} -> StackIO Integer n
  neg {n = S n'} = do
    SCmd doNeg
    showTop
  neg = do
    PutStr "Stack is empty"
    calc

  -- Ex 1.
  -- This is subtract subtracts _top_ element from previous one.
  sub : {n : Nat} -> StackIO Integer n
  sub {n = S (S n')} = do
    SCmd (doNeg >> doAdd)
    showTop
  sub = do
    PutStr "Fewer than two items on stack"
    calc

  -- Ex 1.
  mul : {n : Nat} -> StackIO Integer n
  mul {n = S (S n')} = do
    SCmd doMul
    showTop
  mul = do
    PutStr "Fewer than two items on stack"
    calc

  -- Ex 3.
  dsc : {n : Nat} -> StackIO Integer n
  dsc {n = S n'} = do
    x <- SCmd Pop
    PutStr ("Discarded " ++ show x)
    calc
  dsc = do
    PutStr "Stack is empty, nothing to discard"
    calc

  -- Ex 4.
  dup : {n : Nat} -> StackIO Integer n
  dup {n = S n'} = do
    x <- SCmd Top
    SCmd (Push x)
    calc
  dup = do
    PutStr "Stack is empty, nothing to duplicate"
    calc

  calc : {n : Nat} -> StackIO Integer n
  calc = do
    inp <- GetStr
    case strToInput inp of
         Right Add => add
         Right Sub => sub
         Right Mul => mul
         Right Neg => neg
         Right Dsc => dsc
         Right Dup => dup
         Right (Number x) => do
           SCmd (Push x)
           calc
         Left err => do
           PutStr err
           calc
