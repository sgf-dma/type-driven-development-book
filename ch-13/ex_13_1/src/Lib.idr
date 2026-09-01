module Lib

-- Ex 1.
data DoorState = DoorOpen | DoorClosed

data DoorCmd : Type -> DoorState -> DoorState -> Type where
  Open : DoorCmd () DoorClosed DoorOpen
  Close : DoorCmd () DoorOpen DoorClosed
  RingBell : DoorCmd () a a

  Pure : ty -> DoorCmd ty state state
  (>>=) : DoorCmd a state1 state2 -> (a -> DoorCmd b state2 state3) -> DoorCmd b state1 state3

namespace DoorCmd
  export
  (>>) : DoorCmd a state1 state2 -> DoorCmd b state2 state3 -> DoorCmd b state1 state3
  d1 >> d2 = d1 >>= \_ => d2

doorProg : DoorCmd () DoorClosed DoorClosed
doorProg = do
  RingBell
  Open
  RingBell
  Close

-- Ex. 2
data GuessCmd : Type -> Nat -> Nat -> Type where
  Try : Integer -> GuessCmd Ordering (S n) n
  PureGuess : ty -> GuessCmd ty state state

namespace GuessCmd
  export
  (>>) : GuessCmd a state1 state2 -> GuessCmd b state2 state3 -> GuessCmd b state1 state3

threeGuesses: GuessCmd () 3 0
threeGuesses = do
  Try 10
  Try 20
  Try 15
  PureGuess ()

--noGuesses : GuessCmd () 0 0
--noGuesses = do
--  Try 10
--  PureGuess ()

-- Ex. 3
data Matter = Solid | Liquid | Gas

data MatterCmd : Type -> Matter -> Matter -> Type where
  Melt : MatterCmd () Solid Liquid
  Boil : MatterCmd () Liquid Gas
  Condense : MatterCmd () Gas Liquid
  Freeze : MatterCmd () Liquid Solid

namespace MatterCmd
  export
  (>>) : MatterCmd a s1 s2 -> MatterCmd b s2 s3 -> MatterCmd b s1 s3

iceSteam : MatterCmd () Solid Gas
iceSteam = do
  Melt
  Boil

steamIce : MatterCmd () Gas Solid
steamIce = do
  Condense
  Freeze

--overMelt : MatterCmd () Solid Gas
--overMelt = do
--  Melt
--  Melt

