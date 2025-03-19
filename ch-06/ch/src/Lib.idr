module Lib

import Data.Vect
import Data.String
import Data.List

Position : Type
Position = (Double, Double)

Polygon : Nat -> Type
Polygon n = Vect n Position

tri : Polygon 3
tri = [(0, 0), (1, 1), (2, 2)]

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int

getStringOrInt : (b : Bool) -> StringOrInt b
getStringOrInt False = "Ninety four"
getStringOrInt True = 94

valToString : (b : Bool) -> StringOrInt b -> String
valToString False str = trim str
valToString True n = cast n

valToString2 : (b : Bool) -> (case b of
                                  False => String
                                  True  => Int) -> String
valToString2 False y = trim y
valToString2 True y = cast y

valToString3 : {t : Type} -> t -> String
valToString3 {t = Int} y = show y
valToString3 {t = String} y = trim y
valToString3 {t = _} _ = "Not implemented"

typeRep : Type -> String

searchTy : List Type -> Type -> Maybe Type
--searchTy ts t0 = case findIndex (\t => typeRep t0 == typeRep t) ts of
--                     Nothing => Nothing
--                     Just i => let y = index' ts i in Just y
searchTy ts t0 = index' ts <$> findIndex (\t => typeRep t0 == typeRep t) ts

{-
partial searchTy : Show a => List a -> a -> Maybe a
searchTy ts t0 = case findIndex (\t => show t0 == show t) ts of
                     Nothing => Nothing
                     Just i => let y = index' ts i in ?c --Just (index i ts)
                     -}

{-
showType : Type -> String
showType Int = "Int"
showType (Nat -> b) = ?c2
showType _ = "None"
-}

valToString4 : {t : Type} -> t -> String
--valToString4 y = ?c1 --show y
--valToString4 _ = ?c3 --"Not implemented"

AdderType : Nat -> Type
AdderType Z = Int
AdderType (S n) = (y : Int) -> AdderType n

adder : (n : Nat) -> Int -> AdderType n
adder Z acc = acc
adder (S n) acc = \y => adder n (y + acc)

AdderType' : Nat -> Type -> Type
AdderType' Z a = a
AdderType' (S n) a = a -> AdderType' n a

adder' : Num a => (n : Nat) -> a -> AdderType' n a
adder' Z acc = acc
adder' (S n) acc = \y => adder' n (y + acc)

data Format = Number Format
            | Str Format
            | Lit String Format
            | End

PrintfType : Format -> Type
PrintfType (Number fmt) = Int -> PrintfType fmt
PrintfType (Str fmt) = String -> PrintfType fmt
PrintfType (Lit _ fmt) = PrintfType fmt
PrintfType End = String

printfFmt : (fmt : Format) -> String -> PrintfType fmt
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc = \s => printfFmt fmt (acc ++ s)
printfFmt (Lit str fmt) acc = printfFmt fmt (acc ++ str)
printfFmt End acc = acc

toFormat : List Char -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: xs) = Number (toFormat xs)
toFormat ('%' :: 's' :: xs) = Str (toFormat xs)
--toFormat ('%' :: xs) = Lit "%" (toFormat xs)
toFormat (c :: xs) = case toFormat xs of
                          Lit s fmt => Lit (c `strCons` s) fmt
                          fmt => Lit (singleton c) fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""

-- Unlike 'Format' here show functions are embedded in data constructors.
-- That's probably not very good, but..
data Format2 = Number2  (String -> Int -> String) Format2
             | Str2     (String -> String -> String) Format2
             | Unknown2 (forall a. String -> a -> String) Format2
             | End2 (String -> String)

toFormat2 : String -> Format2
toFormat2 str =
  let (ls, rs) = span (/= '%') str
  in  case strM rs of
           StrNil => End2 (++ ls)
           StrCons _ rs' => case strM rs' of
                  StrNil => End2 (++ ls ++ "%")
                  StrCons 'd' rs'' => Number2 (\acc, i => acc ++ ls ++ show i) (toFormat2 rs'')
                  StrCons 's' rs'' => Str2 (\acc, s => acc ++ ls ++ s) (toFormat2 rs'')
                  StrCons  c  rs'' => Unknown2 (\acc, _ => acc ++ ls ++ "%" ++ singleton c) (toFormat2 rs'')

PrintfType2 : Format2 -> Type
PrintfType2 (Number2 _ fmt) = Int -> PrintfType2 fmt
PrintfType2 (Str2 _ fmt) = String -> PrintfType2 fmt
PrintfType2 (Unknown2 _ fmt) = {a : Type} -> a -> PrintfType2 fmt
PrintfType2 (End2 _) = String

-- Therefore, because show functions are embedded in data constructors,
-- 'printfFmt2' becomes just an evaluator (or runner) for already defined
-- functions. It does not contain any logic. Thus, iteration over each
-- constructor here is meaningless. So, v4 is probably a better implementation
-- of such solution.
printfFmt2 : (fmt : Format2) -> String -> PrintfType2 fmt
printfFmt2 (Number2 f fmt)  acc = printfFmt2 fmt . f acc
printfFmt2 (Str2 f fmt)     acc = printfFmt2 fmt . f acc
printfFmt2 (Unknown2 f fmt) acc = printfFmt2 fmt . f acc
printfFmt2 (End2 f)         acc = f acc

printf2 : (fmt : String) -> PrintfType2 (toFormat2 fmt)
printf2 fmt = printfFmt2 _ ""


data Format3 : Type -> Type where
  Arg3 : (String -> a -> String) -> {b : Type} -> Format3 b -> Format3 a
  Unknown3 : (forall a. String -> a -> String) -> {b : Type} -> Format3 b -> Format3 a
  End3 : (String -> String) -> Format3 ()

partial toFormat3 : String -> (a ** Format3 a)
toFormat3 str = case span (/= '%') str of
                    (ls, "") => (() ** End3 (const ls))
                    (ls, "%") => (() ** End3 (const (ls ++ "%")))
                    (ls, rs) => case unpack rs of
                                    (_ :: 'd' :: rs') => let (b ** p) = toFormat3 (pack rs') in (Int ** Arg3 (\acc, y => acc ++ ls ++ show y) p)
                                    (_ :: 's' :: rs') => let (b ** p) = toFormat3 (pack rs') in (String ** Arg3 (\acc, y => acc ++ ls ++ y) p)
                                    --(_ :: s :: rs') => let (b ** p) = toFormat3 (pack rs') in (a ** Unknown3 (\acc, y => acc ++ ls ++ "%" ++ show s) p)
                                    _ => (() ** End3 id)

-- I probably can call 'PrintfType3' with the result of 'toFormat3', but i
-- need to decompose dependent pair somehow. Thus, it's simpler to just write
-- this decomposition beforehand as done in v4.
PrintfType3 : {a : Type} -> Format3 a -> Type
PrintfType3 (Arg3 _ {b = b} p) = a -> PrintfType3 {a = b} p
PrintfType3 (Unknown3 _ {b = b} p) = {c : Type} -> c -> PrintfType3 {a = b} p
PrintfType3 (End3 _) = String

-- Here, unlike v2, all known specifiers are gathered into single constructor
-- with embedded show function - 'Arg4'. Therefore, i no longer have identical
-- cases iterating over data constructors in 'printfFmt4'. So, i think, this
-- is the best possible implementation of the solution with show function
-- embedded into data constructor. But what solution is better - author's or
-- this - is another question.
data Format4 : Type -> Type where
  Arg4 : (String -> a -> String) -> (b ** Format4 b) -> Format4 a
  --Unknown4 : (String -> String) -> (b ** Format4 b) -> {a : Type} -> Format4 a
  Unknown4 : (String -> String) -> (b ** Format4 b) -> Format4 ()
  End4 : (String -> String) -> Format4 ()

toFormat4 : String -> (a ** Format4 a)
toFormat4 str =
  let (ls, rs) = span (/= '%') str
  in  case strM rs of
           StrNil => MkDPair _ (End4 (++ ls))
           StrCons _ rs' => case strM rs' of
                  StrNil => (_ ** End4 (++ ls ++ "%"))
                  StrCons 'd' rs'' => MkDPair Int (Arg4 (\acc, i => acc ++ ls ++ show i) (toFormat4 rs''))
                  StrCons 's' rs'' => (String ** Arg4 (\acc, s => acc ++ ls ++ s) (toFormat4 rs''))
                  StrCons  c  rs'' => (_ ** Unknown4 (\acc => acc ++ ls ++ "%" ++ singleton c) (toFormat4 rs''))

PrintfType4 : (a ** Format4 a) -> Type
PrintfType4 (a ** (Arg4 _ p)) = a -> PrintfType4 p
PrintfType4 (_ ** (Unknown4 _ p)) = {a : Type} -> a -> PrintfType4 p
PrintfType4 (_ ** End4 _) = String

printfFmt4 : (fmt : (a : Type ** Format4 a)) -> String -> PrintfType4 fmt
printfFmt4 (_ ** Arg4     f fmt) acc = printfFmt4 fmt . f acc
printfFmt4 (_ ** Unknown4 f fmt) acc = const (printfFmt4 fmt (f acc))
printfFmt4 (_ ** End4 f) acc = f acc

printf4 : (fmt: String) -> PrintfType4 (toFormat4 fmt)
printf4 fmt = printfFmt4 _ ""

-- This is version v4 without type argument (as in v2 or author's version).
-- But i can't write 'toFormat5' for it, because in 'd' case i have nothing,
-- which can restrict type of 'i'. Particularly, i can't deduce 'Show'
-- instance for 'i'.
data Format5 = Arg5 (String -> a -> String) Format5
             | Unknown5 (String -> String) Format5
             | End5 (String -> String)

partial toFormat5 : String -> Format5
toFormat5 str =
  let (ls, rs) = span (/= '%') str
  in  case strM rs of
           StrNil => End5 (++ ls)
           StrCons _ rs' => case strM rs' of
                  StrNil => End5 (++ ls ++ "%")
                  -- Does not compile.
                  --StrCons 'd' rs'' => Arg5 (\acc, i => acc ++ ls ++ show i) (toFormat5 rs'')
                  StrCons 's' rs'' => Arg5 (\acc, s => acc ++ ls ++ s) (toFormat5 rs'')
                  StrCons  c  rs'' => Unknown5 (\acc => acc ++ ls ++ "%" ++ singleton c) (toFormat5 rs'')

-- That means, that if i don't want to use type parameter in 'Format', i may
-- have only two possible implmentation:
--  * author's with show functions written in 'printfFmt'
--  * or my v2 with duplicate cases in 'printfFmt'.
-- But the key point to be able to implement such solution is per-type data
-- constructor, like 'Number' and 'Str', not a single constructor for all
-- types, like 'Arg'.
--
-- If i want a single constructor for all types, like 'Arg' (e.g. to eliminate
-- duplicate cases in my v2), i need a type parameter. Otherwise, i won't be
-- able to elaborate about types of argument and, thus, can't deduce 'Show'
-- instance for it.
