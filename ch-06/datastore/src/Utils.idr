module Utils

import Data.String
import Data.Fin
import Data.Vect
import Control.Category
import Control.Monad.Writer
import Data.Morphisms
import Control.Arrow

export infixr 9 *
export infixr 9 .*

-- Conversion of Nat to Fin without Maybe. Version with pattern matching.
export
total natToFin2 : (m : Nat) -> (n : Nat) -> Fin (maximum (S m) n)
natToFin2 Z Z = FZ {k = Z}
natToFin2 Z (S k) = FZ {k = k}
natToFin2 (S k) Z = FS (natToFin2 k Z)
natToFin2 (S k) (S t) = FS (natToFin2 k t)

-- Convert Nat to minimal possible Fin.
export
total natToFinMin : (k : Nat) -> Fin (S k)
natToFinMin Z     = FZ {k = Z}
natToFinMin (S t) = FS (natToFinMin t)

total max' : Nat -> Nat -> Nat
max' m n = case compare m n of
                LT => n
                EQ => m
                GT => m

-- Version of natToFin2 based on compare without explicit pattern matching.
export
total natToFin3 : (m : Nat) -> (n : Nat) -> Fin (max' (S m) n)
natToFin3 m Z = natToFinMin m
natToFin3 m n@(S t) with (compare (S m) n)
  _ | LT = natToFinMin t
  _ | EQ = natToFinMin m
  _ | GT = natToFinMin m

-- Add empty list elements to vector if needed, so the vector will contain
-- element with index m.
export
padEmpty : (m : Nat) -> {t : Nat} -> Vect t (List a) -> Vect (maximum (S m) t) (List a)
padEmpty Z     {t = Z}   vs = [[]]
padEmpty Z     {t = S _} vs = vs
padEmpty (S k) {t = Z}   _  = go (S (S k))
  where
    go : (n : Nat) -> Vect n (List a)
    go Z = []
    go (S k) = [] :: go k
padEmpty (S k) {t = S t} (v :: vs) = v :: padEmpty k vs

-- Match closing parenthesis.
export
closeParen : (String -> Maybe (a, String)) -> String -> Maybe (a, String)
closeParen parse input = do
  (x, rest) <- parse input
  let rest' = ltrim rest    -- Accept ')' with leading spaces.
  case strM rest' of
       StrCons ')' rest2 => pure (x, rest2)
       _ => Nothing

-- Parse parenthesis around expression parsed by another parser 'parse'.
export
parseParens : (parse : String -> Maybe (a, String))
            -> (input : String) -> Maybe (a, String)
parseParens parse input =
  -- I can't `strM (ltrim input)`, because `ltrim` is implemented in terms of
  -- `asList`, which, in turn, in terms of `strM` and.. well, this won't
  -- typecheck for some reason.
  let input' = ltrim input
  in  case strM input' of
           StrCons '(' rest => closeParen parse rest
           _ => Nothing

-- Composition of dependent functions.
export
(*) :  {0 b : a -> Type} -> ({0 x : a} -> b x -> c) -> ((x : a) -> b x) -> a -> c
(*) g f y = g (f y)

export
(.*) : forall b, c. ({0 x : a} -> b x -> c x) -> ((x : a) -> b x) -> (y : a) -> c y
(.*) g f y = g (f y)

-- Experiments with "inventing" combinator, which may capture following
-- pattern:
--
--      f >>> second f >>> second (second f) >>> ...

-- Apply function 'f' specified number of times.
public export
applyN : Nat -> (a -> a) -> a -> a
applyN Z _ x = x
applyN (S n) f x = f (applyN n f x)

-- Useless implementation, because function `f` has no use for its first
-- argument. It will always be essentially just 'const MkT', i.e. just
-- constructor of type `t`. And, also, function `g` runs only once.
iterateN1 : (n : Nat)
          -> {t : Type -> Type}
          -> (f : forall a', b'. (a' -> b') -> (b' -> t b'))
          -> (g : a -> b)
          -> (a -> applyN n t b)
iterateN1 Z     _ g = g
iterateN1 (S n) f g = let y = iterateN1 n f g in f y . y
-- Example:
-- iterateN1 3 (const Just) (+1) 4
-- Just (Just (Just 5))

-- This implementation makes more sense, but still quite useless, because `g`
-- still runs only once. I can't apply it second time, because `g` is of type
-- 'a -> b' and i have nothing of type `b -> ..` (function `f` preserves its
-- argument's type a', thus i can't construct with it smth of type `b' ->..`).
iterateN2 : (n : Nat)
          -> {t : Type -> Type}
          -> (f : forall a', b'. (a' -> b') -> (a' -> t b'))
          -> (g : a -> b)
          -> (a -> applyN n t b)
iterateN2 Z     _ g = g
iterateN2 (S n) f g = let y = iterateN2 n f g in f y
-- Example:
-- iterateN2 3 (\f => Just . f) (+1) 4
-- Just (Just (Just 5))

-- Now, this is more interesting, because it runs `g` at each iteration. Why
-- is that? Because now there's no type `b` in function `g` and by using `f` i
-- can construct new function of type 't a -> t (t a)` from function 'g', and
-- it will compose with function `g`. And then i may repeat this again. And
-- because all these new functions are constructed from `g`, each of them will
-- apply `g` internally. Also note, that using 'a -> t a' for 'g' allows to
-- use 'id' as zero case (i.e. do not apply 'g' at 0).
iterateN3 : (n : Nat)
          -> {t : Type -> Type}
          -> (f : forall a', b'. (a' -> b') -> (t a' -> t b'))
          -> (g : a -> t a)
          -> (a -> applyN n t a)
iterateN3 Z     _ _ = id
iterateN3 (S n) f g =
  let y = iterateN3 n f g
  in  f y . g
-- Example:
-- iterateN3 3 (\f, mx => mx >>= \x => Just (f x)) (\x => Just (x+1)) 4
-- Just (Just (Just 7))

-- I may notice, that `f` is essentially just a `map`.
iterateN3' : Functor t => (n : Nat)
          -> (g : a -> t a)
          -> (a -> applyN n t a)
iterateN3' Z     _ = id
iterateN3' (S n) g = map (iterateN3' n g) . g
-- Example:
-- iterateN3' 3 (\x => Just (x+1)) 4
-- Just (Just (Just 7))

-- I may even notice, that `g` type is similar to `pure`, but this is
-- misleading, because `pure` does nothing, though `g` may do something.
iterateN3'2 : forall t. Applicative t => (n : Nat) -> (a -> applyN n t a)
iterateN3'2 Z = id
iterateN3'2 {t = t} (S n) = map (iterateN3'2 n {t = t}) . pure
-- Example:
-- iterateN3'2 {t = Maybe} 3 4
-- Just (Just (Just 4))

-- I may say, that stacking type `t` has no sense and require `t` to be a
-- monad and then join all types `t` into single one and run computation `g`
-- specified number of times.
export
iterateM : Monad m => Nat -> (g : a -> m a) -> (x : a) -> m a
iterateM Z _ = pure
iterateM (S n) g = let h = iterateM n g in  g <=< h
-- Example:
-- iterateM 3 (\x => Just (x+1)) 4
-- Just 7

fix : (Lazy a -> a) -> a
fix f = f (fix f)

-- Or i may use `fix` to do the same.
iterateM' : Monad m
           => (g : a -> m a)
           -> (rec : Lazy (Nat -> (a -> m a)))
           -> Nat -> a -> m a
iterateM' _ _ Z = pure
iterateM' g rec (S n) = let h = rec n in  g <=< h
-- Example:
-- fix (iterateM' (\x => Just (x+1))) 3 4
-- Just 7

-- Alternatively, i may do the same with `Category`. Here i can't join types
-- `t` anymore, but anyway.
export
iterateA : (n : Nat)
          -> {t : Type -> Type}
          -> Category cat => (f : forall a', b'. cat a' b' -> cat (t a') (t b'))
          -> (g : cat a (t a))
          -> cat a (applyN n t a)
iterateA Z     _ _ = id
iterateA (S n) f g = let y = iterateA n f g in  f y . g
-- Example:
-- applyMor (iterateA 3 {t = Maybe} (Mor . map . applyMor) (Mor $ \x => Just (x+1))) 4
-- Just (Just (Just 7))
--
-- or
--
-- applyMor (iterateA 3 (Mor . map {f = Maybe} . applyMor) (Mor $ \x => Just (x+1))) 4

pair2Vect : (n : Nat) -> applyN n (Pair a) b -> (Vect n a, b)
pair2Vect Z x = ([], x)
pair2Vect (S n) (x, zs) = let (vs, y) = pair2Vect n zs in  (x :: vs, y)

-- Uncons specified number of characters.
-- Using `iterateA` i may implement type-safe version, which guarantees in
-- type the specified number of characters. Note, that both `pair2Vect` and
-- `iterateA` take the same `n`, but i may omit it at `iterateA` call and
-- it'll be derived from the type.
export
strUncons1 : (n : Nat) -> String -> Maybe (Vect n Char, String)
strUncons1 n input =
    pair2Vect n <$> applyKleisli (iterateA _ second unconsA) input
  where
    unconsA : Kleislimorphism Maybe String (Char, String)
    unconsA = Kleisli strUncons

-- But using monadic `iterateM` i may only implement version with 'List',
-- because 'WriterT' can't change its writer type on the go.
strUncons2 : (n : Nat) -> String -> Maybe (List Char, String)
strUncons2 n input = swap <$> runWriterT (iterateM n go input)
  where
    go : String -> WriterT (List Char) Maybe String
    go str = case strUncons str of
                  Nothing => writerT Nothing
                  Just (c, rest) => writerT (Just (rest, [c]))
                  --Just (c, rest) => MkWriterT (\cs => Just (rest, cs `snoc` c))

