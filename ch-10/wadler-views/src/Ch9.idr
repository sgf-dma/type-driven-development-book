
module Ch9

import Data.Nat
import Syntax.PreorderReasoning


%default total

data ViewAs : Type -> Type where
  As : (x : a) -> (y : a) -> {auto 0 prf : x = y} -> ViewAs a

viewAs : (x : a) -> ViewAs a
viewAs x = As x x {prf = Refl}

outViewAs : ViewAs a -> a
outViewAs (As x x {prf = Refl}) = x

-- Such definition of 'As' won't refine arguments and, in fact, is not exactly
-- what is wanted: it's not a replacement for 'z@[]', because i need a rewrite
-- by 'prf' to use 'z' in place of '[]'. But still it's close point.
f : (x : List Int) -> Int
f x with (viewAs x)
  f x | As z [] {prf} = ?a1
  f x | As z (_::_) {prf} = ?a2

-- This definition is, in fact, 'Equal' with its contructor 'Refl'.
data ViewAs2 : a -> a -> Type where
  As2 : (x : a) -> ViewAs2 x x

viewAs2 : (x : a) -> ViewAs2 x x

-- It refines patterns, but now i miss the main point: i no longer have a name
-- for entire argument. Well, probably, in Idris only first (non-refinement)
-- version is possible, because, when i refine pattern, Idris wants to rewrite
-- all occurences of refined argument and i lose name for original arg.
f2 : (x : List Int) -> Int
f2 x with (viewAs2 x)
  f2 [] | As2 [] = ?b1
  f2 (_::_) | As2 (_::_) = ?b2

public export
data Parity : Nat -> Type where
  Even : {auto k : Nat} -> Parity (2*k)
  Odd : {auto k : Nat}  -> Parity (2*k + 1)

export
Eq (Parity n) where
  _ == _ = True

export
parity : (x : Nat) -> Parity x
parity Z = Even
parity (S t) =
  case parity t of
       Even {k} => let rr = Odd {k = k}
                       prf : S (k + (k + 0)) === ((k + (k + 0)) + 1)
                       prf = Calc $
                              |~ S (k + (k + 0))
                              ~~ S ((k + (k + 0)) + 0)
                                    ...(rewrite plusZeroRightNeutral (k + (k + 0)) in Refl)
                              ~~ ((k + (k + 0)) + 1)
                                    ...(plusSuccRightSucc (k + (k + 0)) 0)
                   in rewrite prf in rr
       Odd {k} => let rr = Even {k = S k}
                      prf : S ((k + (k + 0)) + 1) === S (k + S (k + 0))
                      prf = Calc $
                              |~ S ((k + (k + 0)) + 1)
                              ~~ S (k + ((k + 0) + 1))
                                    ...(rewrite plusAssociative k (k + 0) 1 in Refl)
                              ~~ S (k + S ((k + 0) + 0))
                                    ...(rewrite plusSuccRightSucc (k + 0) 0 in Refl)
                              ~~ S (k + S (k + 0))
                                    ...(rewrite plusZeroRightNeutral (k + 0) in Refl)
                    in rewrite prf in rr

