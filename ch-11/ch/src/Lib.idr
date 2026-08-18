module Lib

import Data.Bits
import Data.Stream
import Data.List
import Data.Fin
import Data.Nat
import Data.String
import Data.Primitives.Views
import Divides

%default total

-- %auto_lazy off

-- 11.1

partial
countFrom : Integer -> List Integer
countFrom n = n :: countFrom (n + 1)

data InfList : Type -> Type where
  (::) : (val : a) -> Inf (InfList a) -> InfList a

total
countFrom2 : Integer -> InfList Integer
--countFrom2 n = n :: Delay (countFrom2 (n + 1))
countFrom2 n = n :: countFrom2 (n + 1)

total
getPrefix : (count : Nat) -> InfList a -> List a
getPrefix Z _ = []
--getPrefix (S k) (v::infvs) = v :: getPrefix k (Force infvs)
getPrefix (S k) (v::infvs) = v :: getPrefix k infvs

-- Infinite data type _may_ be finite, like this one. And this does not break
-- "productive" claim just because i still need to cover all well-typed
-- inputs. So, in `getPrefix` i need to somehow handle Nil.
-- In other words, `Inf` just makes really infinite values possible in total
-- functions, but does not restrict data type to e.g. only infinite values.
data InfList' : Type -> Type where
  Nil' : InfList' a
  Cons' : (val : a) -> Inf (InfList' a) -> InfList' a

total
countFrom2' : Integer -> InfList' Integer
countFrom2' n = Cons' n (countFrom2' (n + 1))

getPrefix' : (count : Nat) -> InfList' a -> List a
getPrefix' Z _ = []
getPrefix' (S k) Nil' = []
getPrefix' (S k) (Cons' v infvs) = v :: getPrefix' k infvs

total
labelWith : (labels : Stream a) -> (values : List b) -> List (a, b)
labelWith _ [] = []
labelWith (l::ls) (v::vs) = (l, v) :: labelWith ls vs

total
label : List b -> List (Nat, b)
label = labelWith (iterate (+1) 0)

partial
quiz : Stream Nat -> (score : Nat) -> IO ()
quiz (n1 :: n2 :: nums) score
  = do putStrLn ("Score so far: " ++ show score)
       putStr (show n1 ++ " * " ++ show n2 ++ "? ")
       answer <- getLine
       if cast answer == n1*n2
          then do putStrLn "Correct!"
                  quiz nums (score+1)
          else do putStrLn ("Wrong, the answer is " ++ show (n1*n2))
                  quiz nums score

export
randoms : Integer -> Stream Integer
randoms seed =
  let seed' = 1664525 * seed + 1013904223 in (seed' `shiftR` 2) :: randoms seed'

-- Below is my quiz version.
-- Use 'Int16', because otherwise conversion to 'Nat' would take too long.
randomsInt : Int16 -> Stream Int16
randomsInt seed =
  let seed' = 1664525 * seed + 1013904223 in (seed' `shiftR` 2) :: randomsInt seed'

export
randomNats : Int16 -> Stream Nat
randomNats seed = go (randomsInt seed)
  where
    go : Stream Int16 -> Stream Nat
    go (r::rs) = integerToNat (cast {to = Integer} (abs r)) :: go rs

total
ltToFin : {n : Nat} -> n `LT` m -> (k : Fin m ** finToNat k === n)
ltToFin {n = Z} (LTESucc LTEZero) = (FZ ** Refl)
ltToFin {n = S n'} (LTESucc lte) =
  let (rec ** prf) = ltToFin lte in  (FS rec ** cong S prf)

-- I can't prove anything for primitive types. So, just `believe_me` and `assert_total`.
total
intGeZeroLteToNatLTE : {n : Integer} -> ((n >= 0) && (n < m)) === True -> fromInteger n `LT` fromInteger m
intGeZeroLteToNatLTE {n = 0} _ = believe_me (LTESucc {right = fromInteger (m - 1)} LTEZero)
intGeZeroLteToNatLTE {n} prf =
  let rec = assert_total (intGeZeroLteToNatLTE {n = n - 1} {m = m - 1} (believe_me Refl))
      rrr = LTESucc {left = (S (integerToNat (prim__sub_Integer n 1)))}
                    {right = fromInteger (m - 1)}
                    rec
   in believe_me rrr

total export
arithInputs1 : (max : Integer) -> (rs : Stream Integer) -> Stream (Fin (S (fromInteger max)))
-- I should have divided by (max + 1), but then Idris won't be able to solve
-- constraint for 'DivByZero' case with
--
--      Can't solve constraint between: 0 and prim__add_Integer ?max 1.
--
-- probably, because 'prim__add_Integer' is operation on primitive type. This
-- is true for both `with` and `case`.
arithInputs1 max (r::rs') with (divides r max)
  arithInputs1 0 (r::rs') | DivByZero = repeat FZ
  arithInputs1 max ((max*div + rem)::rs') | DivBy div rem prf =
    let prfLt = intGeZeroLteToNatLTE prf
        -- User expects result to be `<= max` according to type, but because
        -- i've divided by `max` remainder is `< max` and in fact now i can't
        -- fix this.
        (rf ** _) = ltToFin prfLt
        -- But i still can't change the type to `Fin (fromInteger max)`
        -- because for 'max==0' i need to return `FZ` anyway, but FZ has type
        -- `Fin (S k)`. So, i may either `weaken` the result (but this
        -- nevertheless does not change the fact, that there'll be no values
        -- equal to `max`). Also, in this case results for max==0 and max==1
        -- will be the same - all zeros:
        --
        --r2 = weaken rf

        -- Or just increase by 1 using `FS`. In this case there'll be values
        -- equal to `max`, but there'll be no 0 at all (only for max==0
        -- there'll be all zeros). The last way was choosen in the book,
        -- probably, because there is no sense in returning 0 for
        -- multiplication quiz.
    in  FS rf :: arithInputs1 max rs'

-- But there is a little sense in negative `max`, so i may try to take Nat
-- instead. And even this simple wrapper requires 'believe_me', because i just
-- can't prove anything about primitive types.
arithInputs1' : (max : Nat) -> (rs : Stream Integer) -> Stream (Fin (S max))
arithInputs1' max rs =
  let r = arithInputs1 (natToInteger max) rs
      prf : max === integerToNat (natToInteger max)
      prf = believe_me (Refl {x = max})
  in rewrite prf in r

-- Or i may try to write whole function with Nat. Note, that here i divide by
-- `S max` and unlike `arithInputs1` zeros are possible here in results for
-- any `max` value.
total export
arithInputs2 : (max : Nat) -> (rs : Stream Integer) -> Stream (Fin (S max))
arithInputs2 max (r::rs') with (divides r (natToInteger (S max)))
  arithInputs2 max ((natToInteger (S max) * div + rem)::rs') | DivBy div rem prf =
    let prfLt = intGeZeroLteToNatLTE prf
        (r2 ** _) = ltToFin prfLt
        prfAddInt : S max === integerToNat (prim__add_Integer 1 (natToInteger max))
        prfAddInt = believe_me (Refl {x = S max})
        in  (rewrite prfAddInt in r2) :: arithInputs2 max rs'
  -- For this impossible case Idris can't solve constraint between: 0 and
  -- prim__add_Integer 1 (natToInteger ?m):
  --
  --        Can't solve constraint between: 0 and prim__add_Integer ?max 1.
  --
  -- probably, the reason is also operation on primitive types. Anyway, this
  -- case is impossible, because `natToInteger` converts all negative integers
  -- to 0 and then i add 1. So divider will be always '>=1'.
  --arithInputs2 m (r::rs') | DivByZero = ?a8
  arithInputs2 m (r::rs') | _ = ?arithInputs2_impossible

-- And, finally, here is version using `divides` for Nat-s. It solves all
-- problems above: it has no `assert_total` or `believe_me`-s, it has no
-- unsolvable constraints and it divides by `S max` and zeros are possible in
-- any results.
total export
arithInputs3 : (max : Nat) ->
               (rs : Stream Nat) -> Stream (Fin (S max))
arithInputs3 Z (r::rs') = repeat FZ
arithInputs3 (S m) (r::rs') with (divides r (S (S m)))
  arithInputs3 (S m) ((S (S m) * div + rem)::rs') | DivBy div rem {prfR} =
    let (r2 ** _) = ltToFin prfR
    in r2 :: (arithInputs3 (S m) rs')

partial
quiz2 : (score : Nat) -> {0 max : Nat} -> Stream (Fin (S max)) -> IO ()
quiz2 score (n1 :: n2 :: nums)
  = do putStrLn ("Score so far: " ++ show score)
       putStr (show n1 ++ " * " ++ show n2 ++ "? ")
       answer <- getLine
       let rightAnswer : Nat = (finToNat n1)*(finToNat n2)
       if cast answer == rightAnswer
          then do putStrLn "Correct!"
                  quiz2 (score+1) nums
          else do putStrLn ("Wrong, the answer is " ++ show rightAnswer)
                  quiz2 score nums

-- 11.2

public export
data InfIO : Type where
  Do : IO a -> (a -> Inf InfIO) -> InfIO

loopPrint : String -> InfIO
loopPrint msg = Do (putStrLn msg) (\_ => loopPrint msg)

partial
run : InfIO -> IO ()
run (Do mx cont) = do
  x <- mx
  let rec = cont x
  run rec

data InfIO2 : Type -> Type where
  Do2 : IO c -> (c -> Inf (InfIO2 b)) -> InfIO2 b

loopPrint2 : String -> InfIO2 ()
loopPrint2 msg = Do2 (putStrLn msg) (\_ => loopPrint2 msg)

partial
run2 : InfIO2 a -> IO a
run2 (Do2 mx f) = do
  x <- mx
  let rec = f x
  run2 rec

export
data Fuel = Dry | More (Lazy Fuel)

total
tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

total export
runFuel : Fuel -> InfIO -> IO ()
runFuel (More fuel) (Do c f) =
  do res <- c
     runFuel fuel (f res)
runFuel Dry p = putStrLn "Out of fuel"

partial export
foreverFuel : Fuel
foreverFuel = More foreverFuel

namespace InfIODo
  export
  (>>=) : IO a -> (a -> Inf InfIO) -> InfIO
  (>>=) = Do

  export
  (>>) : IO a -> Inf InfIO -> InfIO
  (>>) mx mb = Do mx (\_ => mb)

loopPrint' : String -> InfIO
loopPrint' msg = do
  putStrLn msg
  loopPrint' msg

export
quiz2Inf : {0 max : Nat} -> (score : Nat) -> Stream (Fin (S max)) -> InfIO
quiz2Inf score (n1 :: n2 :: nums)
  = do putStrLn ("Score so far: " ++ show score)
       putStr (show n1 ++ " * " ++ show n2 ++ "? ")
       answer <- getLine
       let rightAnswer : Nat = (finToNat n1)*(finToNat n2)
       if cast answer == rightAnswer
          then do putStrLn "Correct!"
                  quiz2Inf (score+1) nums
          else do putStrLn ("Wrong, the answer is " ++ show rightAnswer)
                  quiz2Inf score nums

-- 11.3

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

namespace CommandDo
  export
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind
  export
  (>>) : Command a -> Command b -> Command b
  (>>) ma mb = ma >>= (\_ => mb)

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (Pure x) = pure x
runCommand (Bind c f) = runCommand c >>= \x => runCommand (f x)

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  CDo : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  export
  run : Fuel -> ConsoleIO a -> IO (Maybe a)
  run fuel (Quit val) = do pure (Just val)
  run (More fuel) (CDo c f) = do
    res <- runCommand c
    run fuel (f res)
  run Dry p = pure Nothing

  export
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = CDo
  export
  (>>) : Command a -> Inf (ConsoleIO b) -> ConsoleIO b
  (>>) ma mb = ma >>= (\_ => mb)

data Input = Answer Int | QuitCmd

readInput : (prompt : String) -> Command Input
readInput prompt = do
  PutStr prompt
  answer <- GetLine
  if toLower answer == "quit"
     then Pure QuitCmd
     else Pure (Answer (cast answer))

mutual
  correct : Stream Int -> (score : Nat) -> ConsoleIO Nat
  correct nums score = do
    PutStr "Correct!\n"
    quiz3 nums (score + 1)

  wrong : Stream Int -> Int -> (score : Nat) -> ConsoleIO Nat
  wrong nums ans score = do
    PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
    quiz3 nums score

  quiz3 : Stream Int -> (score : Nat) -> ConsoleIO Nat
  quiz3 (num1 :: num2 :: nums) score = do
    PutStr ("Score so far: " ++ show score ++ "\n")
    answer <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
    case answer of
         Answer answer =>
                    if answer == num1 * num2
                       then correct nums score
                       else wrong nums (num1 * num2) score
         QuitCmd => Quit score
