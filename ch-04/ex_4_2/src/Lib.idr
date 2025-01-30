module Lib

import Data.Vect

%default total

-- Ex 1, 2.
data PowerSource = Petrol | Pedal | Electric

-- From https://github.com/stephen-smith/tdd-idris-ex .
data PowerCapacity : PowerSource -> Type where
  PetrolCap : (fuel : Nat)-> PowerCapacity Petrol
  ChargeCap : (charge : Nat) -> PowerCapacity Electric

data Capacity = CapacityLv

data Vehicle2 : PowerSource -> Maybe Capacity -> Type where
  Bicycle2 : Vehicle2 Pedal Nothing
  --Car : (fuel : Nat) -> Vehicle Petrol
  --Car : (charge : Nat) -> Vehicle Petrol
  Car2 : PowerCapacity p -> Vehicle2 p (Just CapacityLv)
  Bus2 : (fuel : Nat) -> Vehicle2 Petrol (Just CapacityLv)
  Unicycle2 : Vehicle2 Pedal Nothing
  Motorcycle2 : (fuel : Nat) -> Vehicle2 Petrol (Just CapacityLv)
  Tram2 : Vehicle2 Electric Nothing

data ElectricPower = Connected | Rechargeable

data PowerSource3 : Type where
  Petrol3 : PowerSource3
  Pedal3 : PowerSource3
  Electric3 : ElectricPower -> PowerSource3

data PowerCapacity3 : PowerSource3 -> Type where
  PetrolCap3 : (fuel : Nat)-> PowerCapacity3 Petrol3
  ChargeCap3 : (charge : Nat) -> PowerCapacity3 (Electric3 Rechargeable)

data Vehicle3 : PowerSource3 -> Type where
  Bicycle3 : Vehicle3 Pedal3
  Car3 : PowerCapacity3 p -> Vehicle3 p
  Bus3 : (fuel : Nat) -> Vehicle3 Petrol3
  Unicycle3 : Vehicle3 Pedal3
  Motorcycle3 : (fuel : Nat) -> Vehicle3 Petrol3
  Tram3 : Vehicle3 (Electric3 Connected)

partial refuel3 : {cap : PowerCapacity3 p} -> Vehicle3 p -> Vehicle3 p
refuel3 (Motorcycle3 fuel) = Motorcycle3 50
refuel3 (Car3 (PetrolCap3 fuel)) = Car3 (PetrolCap3 100)
refuel3 (Car3 (ChargeCap3 fuel)) = Car3 (ChargeCap3 100)
refuel3 (Bus3 fuel) = Bus3 200
refuel3 Tram3 impossible
refuel3 Bicycle3 impossible
refuel3 Unicycle3 impossible

data Vehicle : PowerSource -> Type where
  Bicycle : Vehicle Pedal
  --Car : (fuel : Nat) -> Vehicle Petrol
  --Car : (charge : Nat) -> Vehicle Petrol
  Car : PowerCapacity p -> Vehicle p
  Bus : (fuel : Nat) -> Vehicle Petrol
  Unicycle : Vehicle Pedal
  Motorcycle : (fuel : Nat) -> Vehicle Petrol
  Tram : Vehicle Electric

wheels : Vehicle pw -> Nat
wheels Unicycle = 1
wheels Bicycle = 2
wheels (Motorcycle _) = 2
wheels (Car _) = 4
wheels (Bus _) = 4
wheels Tram = 4

refuel : {cap : PowerCapacity p} -> Vehicle p -> Vehicle p
refuel (Motorcycle fuel) = Motorcycle 50
refuel (Car (PetrolCap fuel)) = Car (PetrolCap 100)
refuel (Car (ChargeCap fuel)) = Car (ChargeCap 100)
refuel (Bus fuel) = Bus 200
refuel Tram = Tram  -- Incorrect!
refuel Bicycle impossible
refuel Unicycle impossible

-- Ex 3, 4.

export
vectTake : (m : Fin (S n)) -> Vect n a -> Vect (finToNat m) a
vectTake FZ _ = []
vectTake (FS t) (x :: xs) = x :: vectTake t xs

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
sumEntries : Num a => Integer -> {n : Nat} -> Vect n a -> Vect n a -> Maybe a
sumEntries pos xs ys = case integerToFin pos n of
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
sumEntries' : Num a => Integer -> {n : Nat} -> Vect n a -> Vect n a -> Maybe a
sumEntries' pos xs ys = case integerToFin' pos n of
                            Nothing => Nothing
                            Just i => Just (index' i xs + index' i ys)
