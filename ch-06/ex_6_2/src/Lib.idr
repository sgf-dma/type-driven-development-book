module Lib

import Data.String
import Data.Vect

public export
Matrix : Nat -> Nat -> Type
Matrix n m = Vect n (Vect m Double)

testMatrix : Matrix 2 3
testMatrix = [[0, 0, 0], [0, 0, 0]]

data Format = Number Format
            | Str Format
            | Lit String Format
            | Chr Format
            | Float Format
            | End

public export
PrintfType : Format -> Type
PrintfType (Number fmt) = Int -> PrintfType fmt
PrintfType (Str fmt) = String -> PrintfType fmt
PrintfType (Chr fmt) = Char -> PrintfType fmt
PrintfType (Float fmt) = Double -> PrintfType fmt
PrintfType (Lit _ fmt) = PrintfType fmt
PrintfType End = String

printfFmt : (fmt : Format) -> String -> PrintfType fmt
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc = \s => printfFmt fmt (acc ++ s)
printfFmt (Chr fmt) acc = \c => printfFmt fmt (acc ++ "'" ++ singleton c ++ "'")
printfFmt (Float fmt) acc = \d => printfFmt fmt (acc ++ show d)
printfFmt (Lit str fmt) acc = printfFmt fmt (acc ++ str)
printfFmt End acc = acc

public export
toFormat : List Char -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: xs) = Number (toFormat xs)
toFormat ('%' :: 's' :: xs) = Str (toFormat xs)
toFormat ('%' :: 'c' :: xs) = Chr (toFormat xs)
toFormat ('%' :: 'f' :: xs) = Float (toFormat xs)
--toFormat ('%' :: xs) = Lit "%" (toFormat xs)
toFormat (c :: xs) = case toFormat xs of
                          Lit s fmt => Lit (c `strCons` s) fmt
                          fmt => Lit (singleton c) fmt

export
printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""

public export
TupleVect : Nat -> Type -> Type
TupleVect Z _ = ()
TupleVect (S n) a = (a, TupleVect n a)

TupleVect2 : Nat -> Type -> Type
TupleVect2 0 _ = ()
TupleVect2 2 a = (a, a)
TupleVect2 (S n) a = (a, TupleVect2 n a)
