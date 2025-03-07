module Lib

import Data.Vect
import Data.String
import System

printLength : IO ()
printLength = getLine >>= \str => let len = length str in putStrLn (show len)

--read
readNumber : IO (Maybe Nat)
readNumber = do
  str <- getLine
  pure $ if all isDigit (unpack str) then Just (stringToNatOrZ str) else Nothing

readNumbers : IO (Maybe (Nat, Nat))
readNumbers = do
  Just n1 <- readNumber | Nothing => pure Nothing
  Just n2 <- readNumber | Nothing => pure Nothing
  pure (Just (n1, n2))

countdown : Nat -> IO ()
countdown Z = putStrLn "Lift off!"
countdown t@(S sec) = do
  putStrLn (show t)
  usleep 1000000
  countdown sec

countdowns : IO ()
countdowns = do
  putStr "Enter starting number: "
  Just sec <- readNumber | Nothing => countdowns
  countdown sec

readVectLen : (n : Nat) -> IO (Vect n String)
readVectLen Z = pure []
readVectLen (S n') = do
  x <- getLine
  xs <- readVectLen n'
  pure (x :: xs)

data VectUnknown : Type -> Type where
  MkVect : (n : Nat) -> Vect n a -> VectUnknown a

readVectUnknown : IO (VectUnknown String)
readVectUnknown = do
  x <- getLine
  if x == ""
     then pure (MkVect _ [])
     else do
       MkVect _ xs <- readVectUnknown
       pure (MkVect _ (x :: xs))

printVect : Show a => VectUnknown a -> IO ()
printVect (MkVect n xs) = putStrLn ("(" ++ show n ++ ") " ++ show xs)

anyVect : (n : Nat ** Vect n String)
--anyVect = (3 ** ["a", "b", "c"])

mkVect : (n : Nat) -> Type
mkVect n = Vect n String

-- Desugared dependent-pairs.
anyVect' : DPair Nat (\n => Vect n String)
--anyVect' : DPair Nat Lib.mkVect
anyVect' = MkDPair 3 ["a", "b", "c"]
--anyVect' = MkDPair 3 (the (Vect _ _) ["a", "b", "c"])

-- My wrong dpairs implementation. Now the differences should be clearly
-- visible.
data MyPair : a -> Type -> Type where
  MkMyPair : (n : a) -> {b : a -> Type} -> b n -> MyPair n (b n)

--anyVectP : MyPair 3 (Vect 3 String)
--anyVectP = MkMyPair 3 {b = \n => Vect n String} ?d

readVect : IO (n ** Vect n String)
readVect = do
  x <- getLine
  if x == ""
     then pure (_ ** [])
     else do
       (m ** xs) <- readVect
       pure (S m ** x :: xs)

myExactlLength : (len : Nat) -> Vect m a -> Maybe (Vect len a)
myExactlLength Z [] = Just []
myExactlLength Z _  = Nothing
myExactlLength _ []  = Nothing
myExactlLength (S n) (x :: xs) = case myExactlLength n xs of
                                      Nothing => Nothing
                                      Just ys => Just (x :: ys)

zipInputs : IO (Maybe (n ** Vect n (String, String)))
zipInputs = do
  (n ** xs) <- readVect
  (m ** ys) <- readVect
  case myExactlLength n ys of
       Nothing  => pure Nothing
       Just ys' => do
         let zs = zip xs ys'
         pure (Just (n ** zs))
