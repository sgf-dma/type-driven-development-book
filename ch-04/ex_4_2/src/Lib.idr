module Lib

import Data.Vect

%default total

-- Ex 1, 2.

-- Derived from 'ex_4_3.idr' from https://github.com/stephen-smith/tdd-idris-ex .
data ElectricPower = Connected | Rechargeable

data PowerSource : Type where
  Petrol : PowerSource
  Pedal : PowerSource
  Electric : ElectricPower -> PowerSource

data PowerCapacity : PowerSource -> Type where
  PetrolCap : (fuel : Nat)-> PowerCapacity Petrol
  ChargeCap : (charge : Nat) -> PowerCapacity (Electric Rechargeable)

data Vehicle : PowerSource -> Type where
  Bicycle : Vehicle Pedal
  Car : PowerCapacity p -> Vehicle p
  Bus : (fuel : Nat) -> Vehicle Petrol
  Unicycle : Vehicle Pedal
  Motorcycle : (fuel : Nat) -> Vehicle Petrol
  Tram : Vehicle (Electric Connected)

total refuel : {_ : PowerCapacity p} -> Vehicle p -> Vehicle p
refuel (Motorcycle fuel) = Motorcycle 50
refuel (Car (PetrolCap fuel)) = Car (PetrolCap 100)
refuel (Car (ChargeCap fuel)) = Car (ChargeCap 100)
refuel (Bus fuel) = Bus 200
refuel Tram impossible
refuel Bicycle impossible
refuel Unicycle impossible

wheels : Vehicle p -> Nat
wheels Unicycle = 1
wheels Bicycle = 2
wheels (Motorcycle _) = 2
wheels (Car _) = 4
wheels (Bus _) = 4
wheels Tram = 4

-- Ex 3, 4.

export
vectTake : (m : Fin (S n)) -> Vect n a -> Vect (finToNat m) a
vectTake FZ _ = []
vectTake (FS y) (x :: xs) = x :: vectTake y xs

-- Can't typecheck this.
--vectTakeI : (m : Integer) -> Vect n a -> Vect (finToNat (fromInteger {n = S n} m)) a

public export
data Fin' : (n : Nat) -> Type where
    FZ' : Fin' (S k)
    FS' : Fin' k -> Fin' (S k)

public export
finToNat' : Fin' n -> Nat
finToNat' FZ' = Z
finToNat' (FS' m) = S (finToNat' m)

export
vectTake' : (m : Fin' (S n)) -> Vect n a -> Vect (finToNat' m) a
vectTake' FZ' _ = []
vectTake' (FS' t) (x :: xs) = x :: vectTake' t xs

-- Ex 5.
export
sumEntries : Num a => {n : Nat} -> Integer -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys = case integerToFin pos n of
                            Nothing => Nothing
                            Just i => Just (index i xs + index i ys)

integerToFin' : Integer -> (n : Nat) -> Maybe (Fin' n)
integerToFin' _ Z     = Nothing
integerToFin' x n@(S k) = case compare x 0 of
                               LT => Nothing
                               EQ => Just FZ'
                               GT => FS' <$> integerToFin' (x - 1) k

index' : Fin' n -> Vect n a -> a
index' FZ' (x :: xs) = x
index' (FS' t) (_ :: xs) = index' t xs

export
sumEntries' : Num a => {n : Nat} -> Integer -> Vect n a -> Vect n a -> Maybe a
sumEntries' {n} pos xs ys = case integerToFin' pos n of
                            Nothing => Nothing
                            Just i => Just (index' i xs + index' i ys)
