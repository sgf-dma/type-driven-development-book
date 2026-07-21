module Lib

import Data.Fin
import Data.String
import Data.List1
import System.File
import Decidable.Equality

%default total

-- Ex 11.3.1
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

total
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

data Score : Type where
  MkScore : (tot : Nat) -> (right : Fin (S tot)) -> Score

Show Score where
  show (MkScore tot right) = show tot ++ " / " ++ show right

mutual
  correct : Stream Int -> (score : Score) -> ConsoleIO Score
  correct nums (MkScore tot right) = do
    PutStr "Correct!\n"
    quiz3 nums (MkScore (1 + tot) (FS right))

  wrong : Stream Int -> Int -> (score : Score) -> ConsoleIO Score
  wrong nums ans (MkScore tot right) = do
    PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
    quiz3 nums (MkScore (1 + tot) (weaken right))

  quiz3 : Stream Int -> (score : Score) -> ConsoleIO Score
  quiz3 (num1 :: num2 :: nums) score = do
    PutStr ("Score so far: " ++ show score ++ "\n")
    answer <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
    case answer of
         Answer answer =>
                    if answer == num1 * num2
                       then correct nums score
                       else wrong nums (num1 * num2) score
         QuitCmd => do
           PutStr ("Final score " ++ show score ++ "\n")
           Quit score

-- Ex 11.3.2
-- See side-note below about why i need ShellCommand exactly like this.
--
-- So, using book's terminology, this `ShellCommand` type can describe single,
-- finite or infinite sequences of commands. I.e. here i'm not distinguishing
-- between "single of finite sequences" and infinite sequences, like it was
-- done in the book with `Command` and `ConsoleIO` types correspondingly.
--
namespace ShellCommand
  public export
  data ShellCommand : Type -> Type where
    -- These pair of `ReadFile` and `WriteFile` are operations, that can't fail:
    -- `ReadFile` must always returns file content and if i can't do this,
    -- well, i can only stop the entire pipeline, because i just can't get
    -- `String` resulting value out of nowhere.
    ReadFile : (file : String) -> ShellCommand String
    WriteFile : (dst : String) -> (content : String) -> ShellCommand ()

    -- But these pair of `ReadFile` and `WriteFile` are operations, that _can_
    -- fail. So, use these, if you want to continue execution after failure.
    ReadFileE : (file : String) -> ShellCommand (Either FileError String)
    WriteFileE : (dst : String) -> (content : String) -> ShellCommand (Either FileError ())

    IOCmd : (Command a) -> ShellCommand a

    -- This is "quit" effectively.
    Pure : a -> ShellCommand a
    -- I need 'Inf', because i want `shell` to recursively call itself
    -- infinitely. First argument has the type `ShellCommand`, because i
    -- implement all DSL here, in `ShellCommand` type.
    Bind : ShellCommand a -> (a -> Inf (ShellCommand b)) -> ShellCommand b

  export
  (>>=) : ShellCommand a -> (a -> Inf (ShellCommand b)) -> ShellCommand b
  mx >>= f = Bind mx (\x => f x)
  export
  (>>) : ShellCommand a -> Inf (ShellCommand b) -> ShellCommand b
  --(>>) ma mb = ma >>= (\_ => mb)
  (>>) ma mb = Bind ma (\_ => mb)

Functor ShellCommand where
  map f mx = mx >>= \x => Pure (f x)

total
-- I need `Fuel` to recursively call itself with `Inf` argument from `Bind`.
runShellCommand : Fuel -> ShellCommand a -> IO (Either FileError (Maybe a))
-- readFile is not total, so.. just assert, that it does!
runShellCommand _ (ReadFile file) = map Just <$> assert_total (readFile file)
runShellCommand _ (WriteFile file contents) =
  map Just <$> writeFile file contents
runShellCommand _ (ReadFileE file) = do
  errOrContents <- assert_total (readFile file)
  pure (Right (Just errOrContents))
runShellCommand _ (WriteFileE file contents) = do
  errOrSuccess <- writeFile file contents
  pure (Right (Just errOrSuccess))
runShellCommand _ (IOCmd cmd) = Right . Just <$> runCommand cmd
-- This is effectively "quit".
runShellCommand _ (Pure x) = pure (Right (Just x))
runShellCommand Dry (Bind c f) = pure (Right Nothing)
runShellCommand (More fuel) (Bind c f) = do
  res <- runShellCommand (More fuel) c
  case res of
       -- Terminate at first error.
       Left e => pure (Left e)
       Right Nothing => pure (Right Nothing)
       Right (Just x) => runShellCommand fuel (f x)

catFile : (filename : String) -> ShellCommand ()
catFile filename = do
  IOCmd $ PutStr ("Content of " ++ show filename ++ "\n")
  contents <- ReadFile (trim filename)
  IOCmd (PutStr contents)
  IOCmd (PutStr "\n")

copyFile : (dst : String) -> (src : String) -> ShellCommand ()
copyFile dst src = do
  IOCmd $ PutStr ("Copying from " ++ show src ++ " to " ++ show dst ++ "\n")
  contents <- ReadFile src
  WriteFile dst contents
  IOCmd (PutStr "\n")

-- And here're versions, which continue after errors.
withFileE : (filename : String) -> ((contents : String) -> ShellCommand ()) -> ShellCommand ()
withFileE filename f = do
  errOrContents <- ReadFileE (trim filename)
  case errOrContents of
       Left e => IOCmd (PutStr ("Error reading file " ++ show filename ++ " " ++ show e ++ "\n"))
       Right contents => f contents

catFileE : (filename : String) -> ShellCommand ()
catFileE filename = withFileE filename $ \contents => do
  IOCmd $ PutStr ("Content of " ++ show filename ++ "\n")
  IOCmd $ PutStr contents
  IOCmd $ PutStr "\n"

copyFileE : (dst : String) -> (src : String) -> ShellCommand ()
copyFileE dst src = do
  withFileE src $ \contents => do
    errOrSuccess <- WriteFileE dst contents
    case errOrSuccess of
        Left e =>
          IOCmd (PutStr ("Error writing file '" ++ show dst ++ "' " ++ show e ++ "\n"))
        Right _ =>
          IOCmd $ PutStr ("Copying from " ++ show src ++ " to " ++ show dst ++ "\n")

-- Version 1.
total
shell : ShellCommand ()
shell = do
  IOCmd (PutStr "Enter command: ")
  cmdStr <- IOCmd GetLine
  -- I don't have separate `readInput` function and separate type for user
  -- input. Instead, i parse input here and _immediately_ call corresponding
  -- continuation (`catFile`, `copyFile`, etc). This allows to avoid building
  -- `Input` values and then immediately unwrapping them in the caller, like
  -- in version 2 below.
  case span (/= ' ') cmdStr of
       -- Just do not loop further and end here.
       ("exit", "") => Pure ()

       -- These commands terminate session on error.
       ("cat", filename) => do
         catFile (trim filename)
         -- This recursive call is productive, because `shell` here is second
         -- argument to `Bind`, which has Inf type (a -> Inf (ShellCommand b))
         shell
       ("copy", args) => do
          let (src, dst) = trim <$> span (/= ' ') (trim args)
          copyFile dst src
          shell

       -- These commands continue after errors.
       ("catE", filename) => do
         catFileE (trim filename)
         shell
       ("copyE", args) => do
          let (src, dst) = trim <$> span (/= ' ') (trim args)
          copyFileE dst src
          shell

       _ => do
         IOCmd (PutStr "Unknown command\n")
         shell

partial
mainShell : IO ()
mainShell = do
  errOrNot <- runShellCommand forever shell
  case errOrNot of
       Left e => putStrLn ("Error: " ++ show e)
       Right Nothing => putStrLn "Nothing to say.."
       Right (Just x) => putStrLn "Finished"

-- Version 2. Here i'll use separate type for valid input as was in the book.
data ShellInput : Type where
  Cat : (filename : String) -> ShellInput
  Copy : (dst : String) -> (src : String) -> ShellInput
  Exit : ShellInput

total
readShellInput : ShellCommand ShellInput
readShellInput = do
  IOCmd (PutStr "Enter command: ")
  cmdStr <- IOCmd GetLine
  case span (/= ' ') cmdStr of
       ("exit", "") => Pure Exit
       ("cat", filename) => Pure (Cat filename)
       ("copy", args) =>
          let (src, dst) = trim <$> span (/= ' ') (trim args)
          in  Pure (Copy dst src)
       _ => do
         IOCmd (PutStr "Unknown command\n")
         readShellInput

total
shell2 : ShellCommand ()
shell2 = do
  cmd <- readShellInput
  -- So, here i split input parsing into `readShellInput` function. But what i
  -- get?
  -- - `ShellInput` values are used just to wrap parsed data in
  -- `readShellInput` and then immediately unwrap it back in the `shell2`.
  -- - `shell2` is shallow.
  -- I don't think, this is an improvement in any way.
  case cmd of
       Exit => Pure ()
       Cat filename => catFile filename >> shell2
       Copy dst src => copyFile dst src >> shell2


-- Side note: Here is the key concepts about why i need `Inf`.

-- For regular type 'Do'..
data Do1 : Type -> Type where
  Bind1 : Do1 a -> (a -> Do1 b) -> Do1 b
  -- Even if type construtor has 'Lazy' argument, this does not matter,
  -- because 'Lazy' argument still considered smaller, than original.
  --Bind1 : Do1 a -> (a -> Lazy (Do1 b)) -> Do1 b
  Pure1 : a -> Do1 a

namespace Do1ns
  export
  (>>=) : Do1 a -> (a -> Do1 b) -> Do1 b
  (>>=) = Bind1
  export
  (>>) : Do1 a -> Do1 b -> Do1 b
  (>>) ma mb = ma >>= (\_ => mb)

-- I don't need 'Fuel' at all in `run`! I may safely call `run` recursively
-- for both arguments of `Bind` constructor and they (arguments) will be
-- considered _smaller_.
total
run1 : Do1 a -> IO a
run1 (Pure1 x) = pure x
run1 (Bind1 mx f) = do
  x <- run1 mx
  run1 (f x)

-- But i can't write infinite function, well, because it indeed won't terminate.
partial
loop1 : Nat -> Do1 Nat
loop1 x = Bind1 (Pure1 x) (\_ => loop1 x)

-- Therefore, the only way to make `loop` total is to use reducing argument.
-- Effectively, the same as `Fuel`.
total
loop1' : Nat -> Do1 Nat
loop1' Z = Pure1 Z
loop1' (S t) = Bind1 (Pure1 t) (\_ => loop1' t)

-- But if i add `Inf` type annotation for continuation in 'Bind'..
data Do2 : Type -> Type where
  -- Note the type of continuation's resulting value: it's the same as
  -- original. See below why.
  Bind2 : Do2 a -> (a -> Inf (Do2 a)) -> Do2 a
  Pure2 : a -> Do2 a

-- I can even use do notation for such `Bind` definition! Just make sure
-- to define (>>=) differently, without changing result type.
namespace Do2ns
  export
  (>>=) : Do2 a -> (a -> Inf (Do2 a)) -> Do2 a
  (>>=) = Bind2
  --mx >>= f = Bind2 mx (\x => f x)
  export
  (>>) : Do2 a -> Inf (Do2 a) -> Do2 a
  (>>) ma mb = ma >>= (\_ => mb)

-- I can run infinite function! Because now the `loop` is productive.
total
loop2 : Nat -> Do2 Nat
--loop2 x = Bind2 (Pure2 x) (\_ => loop2 x)
loop2 x = do
  Pure2 x
  loop2 x

-- Though, the reverse won't work, because here i try to recurse infinitely
-- _not_ in the `Inf` argument.
partial
loop2' : Nat -> Do2 Nat
loop2' x = Bind2  (loop2' x) (\x' => Pure2 x')

-- But i may fix it by calling on the non-Inf place _another_ function, which
-- is total (by productive reason) and is essentially the same.
total
loop2'2 : Nat -> Do2 Nat
--loop2'2 x = Bind2  (loop2 x) (\x' => Pure2 x')
loop2'2 x = do
  x' <- loop2 x
  Pure2 x'

-- Now simple `run` definition as was used for `Do1` won't work, because
-- argument `f x` is no longer smaller, than original, and recursive call
-- `run2 (f x)` is potentially infinite.
partial
run2 : Do2 a -> IO a
run2 (Pure2 x) = pure x
run2 (Bind2 mx f) = do
  x <- run2 mx
  run2 (f x)

-- So, now i need `Fuel` to make `run` total..
total
run2' : Fuel -> Do2 a -> IO a
-- I don't need to check how many `Fuel` i have, if i have `Pure` value,
-- because there's no infinite arguments in `Pure`.
run2' _ (Pure2 x) = pure x
-- I'm calling `run` with no fuel! And this's not a problem, because argument
-- `mx` is _smaller_, than original value. After all, i need Fuel not to count
-- _every_ `run` iteration, but to count `run` calls with _infinite_
-- arguments.
-- Also, note, that if continuation changes the type (i.e. has the type `a -> Do2 b`,
-- as it should) i can't call `run2' Dry mx` here, because it returns value
-- of type `Do2 a`, but i need `Do2 b`.
run2' Dry (Bind2 mx f) = run2' Dry mx
run2' (More fuel) (Bind2 mx f) = do
  -- And here i'm also calling `run` _without_ decreasing fuel, because
  -- argument `mx` has no `Inf` qualifier and is already smaller, than
  -- original 'Do2' value.
  x <- run2' (More fuel) mx
  -- But argument `f x` is no longer smaller, than original `Bind2 mx f`,
  -- therefore i need to decrease fuel by one.
  run2' fuel (f x)

-- And this is version of `Do2` with continuation changing the resulting type
-- (as it was in `Do1`).
data Do3 : Type -> Type where
  Bind3 : Do3 a -> (a -> Inf (Do3 b)) -> Do3 b
  Pure3 : a -> Do3 a

namespace Do3ns
  export
  (>>=) : Do3 a -> (a -> Do3 b) -> Do3 b
  mx >>= f = Bind3 mx (\x => f x)
  export
  (>>) : Do3 a -> Do3 b -> Do3 b
  (>>) ma mb = ma >>= (\_ => mb)

total
run3' : Fuel -> Do3 b -> IO (Maybe b)
run3' _ (Pure3 x) = pure (Just x)
-- I can't make a value of type `b` here, because i have no fuel to call `run`
-- recursively with `f x`, so.. well, one of the ways to fix this is to use
-- `Maybe`.
run3' Dry (Bind3 mx f) = pure Nothing
run3' (More fuel) (Bind3 mx f) = do
  maybe_x <- run3' (More fuel) mx
  case maybe_x of
       Nothing => pure Nothing
       Just x => run3' fuel (f x)

total
loop3 : Nat -> Do3 Nat
loop3 x = Bind3 (Pure3 x) (\_ => loop3 x)

-- So, the bottom line is:
-- - If i need to make real infinite function generating value of some type, i
-- need to use `Inf` on the corresponding type constructor argument and i need
-- `Fuel` in `run`.
-- - If i don't need infinite functions, i do need neither `Inf`, nor `Fuel`.
--
-- So, designing of DSL `Do`-like types should start from actual function(s),
-- but not from `Do`-like type and `run` definitions.


-- Not used.

-- (see 'PrefixList' type below)
-- Do i really need both prefix and list in type? Here is the answer:
data WrongPrefixList : List a -> Type where
  WrNoPrefixL : WrongPrefixList xs
  WrHasPrefixL : (pref : List a) -> (rest : List a) -> WrongPrefixList (pref ++ rest)

wrongPrefixList : Eq a => (pref : List a) -> (xs : List a) -> WrongPrefixList xs
wrongPrefixList [] xs = WrHasPrefixL [] xs
wrongPrefixList (_::_) [] = WrNoPrefixL
wrongPrefixList (p::ps) (x::xs') =
  case wrongPrefixList ps xs' of
    WrNoPrefixL => WrNoPrefixL
    -- I don't check whether 'p == x', but still result type checks. Why is
    -- that? Recursive call `wrongPrefixList ps xs'` proofs, that
    --
    --      xs' === ps' ++ rest
    --
    -- and i need a result for `x::xs'`, therefore result type here is
    --
    --      WrongPrefixList (x :: (ps' ++ rest))
    --
    -- and _nothing_ stops me from just specifying correct prefix to satisfy
    -- the type for `WrHasPrefixL` constructor, without even checking does
    -- this prefix really match the real `p::ps` prefix or not. (see below
    -- conitnuation)
    WrHasPrefixL ps' rest => WrHasPrefixL (x::ps') rest

-- View list as some (predefined) prefix and the rest.
public export
data PrefixList : (pref : List a) -> List a -> Type where
  NoPrefixL : PrefixList pref xs
  HasPrefixL : (pref : List a) -> (rest : List a) -> PrefixList pref (pref ++ rest)

export
prefixList : DecEq a => (pref : List a) -> (xs : List a) -> PrefixList pref xs
prefixList [] xs = HasPrefixL [] xs
prefixList (_::_) [] = NoPrefixL
prefixList (p::ps) (x::xs') =
  case p `decEq` x of
    No neq => NoPrefixL
    Yes eq => case prefixList ps xs' of
      NoPrefixL => NoPrefixL
      HasPrefixL ps' rest =>
        -- But if i have prefix mentioned in type, than result type does not
        -- change:
        --
        --      PrefixList (p::ps) (x :: (ps' ++ rest))
        --
        -- but the value _constructed by_ `HasPrefixL` does! Now it has the
        -- type
        --
        --      res : PrefixList (x :: ps') (x :: (ps' ++ ?rest))
        --
        -- and i should prove, that `p === x` to actually use this value as a
        -- result of the function.
        let res = HasPrefixL (x::ps') rest
        in rewrite eq in res

-- The same view for Strings.
public export
data PrefixString : (pref : String) -> String -> Type where
  NoPrefixS : PrefixString pref xs
  HasPrefixS : (pref : String) -> (rest : String) -> PrefixString pref (pref ++ rest)

-- Following two lemmas can't be proved for primitive types.
strNilAppend : (xs : String) -> "" ++ xs = xs
strNilAppend xs = believe_me (Refl {x = xs})

strAppendAssoc : (0 x : Char) -> (0 xs, zs : String) -> x `strCons` (xs ++ zs) = (x `strCons` xs) ++ zs
strAppendAssoc x xs zs = believe_me (Refl {x = x `strCons` (xs ++ zs)})

export
prefixString : (pref : String) -> (xs : String) -> PrefixString pref xs
prefixString pref xs =
  case strM pref of
    StrNil => rewrite sym (strNilAppend xs) in HasPrefixS "" xs
    StrCons p ps => case strM xs of
      StrNil => NoPrefixS
      StrCons x xs' =>
        case p `decEq` x of
          No neq => NoPrefixS
          -- I can't prove totality either, because String is primitive type.
          Yes eq => case assert_total (prefixString ps xs') of
            NoPrefixS => NoPrefixS
            HasPrefixS ps' rest =>
              let res = HasPrefixS (p `strCons` ps') rest
              in  rewrite (sym eq) in
                  rewrite strAppendAssoc p ps' rest in
                          res

