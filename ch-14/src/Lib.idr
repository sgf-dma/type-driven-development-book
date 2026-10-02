module Lib

import Data.Fin
import Data.Vect
import Data.Stream

%default total

data DoorState = DoorClosed | DoorOpen

data DoorResult = OK | Jammed

tryOpen : DoorResult -> DoorState
tryOpen OK = DoorOpen
tryOpen Jammed = DoorClosed

data DoorCmd2 : Type -> DoorState -> DoorState -> Type where
  -- This definition won't work, because constructor or type arguments
  -- represent what is known at _value construction_ time. I.e. such
  -- definition mean, that when i tell, that i _want_ to open the door (by
  -- using Open constructor), i _already know_ the result (whether it's jammed
  -- or not). See `doorProg` below for how the actual program should look
  -- like. With this `Open` definition instead of
  --
  --        doorProg = do
  --          RingBell
  --          x <- Open
  --
  -- i'll have
  --
  --        doorProg = do
  --          RingBell
  --          Open Jammed   -- or Open OK
  --
  -- which has no sense. Result of the action `Open` should only be known in
  -- the function following `Open`, when `run` will execute some action in IO
  -- corresponding to `Open` and send its result to the following function.
  Open2 : (r : DoorResult) -> DoorCmd2 () DoorClosed (tryOpen r)
  Close2 : DoorCmd2 () DoorOpen DoorClosed
  RingBell2 : DoorCmd2 () DoorClosed DoorClosed
  Pure2 : ty -> DoorCmd2 ty state state
  Bind2 : DoorCmd2 a state1 state2 -> (a -> DoorCmd2 b state2 state3) -> DoorCmd2 b state1 state3

data DoorCmd : (ty : Type) -> DoorState -> (ty -> DoorState) -> Type where
  -- As noted previously, constructor arguments or type arguments are things,
  -- which are known at _value construction_ time. In case of `Open` this
  -- means at the time, when i _want_ to open the door (not when i've already
  -- opened it). Therefore, at the time when i only _want_ to open the door,
  -- i know the inital state `DoorClosed` and _the function_, which will
  -- determine final state based on opening result. So, this is why final
  -- state should be a function.
  --
  -- Second, final state concrete value does not matter. This means, that
  -- though it may seem, that `Open` action resulting _value_ is not directly
  -- bound to state function: indeed, it's a function, so why should i apply
  -- it to the result of `Open` and not to any other value, after all? -
  -- that's not the case, because _at the Open time_ i don't care to which
  -- value state function will be applied at all! `Open` constructor type by
  -- itself does not restrict to which value state function will be applied,
  -- it just gives the function. This restriction will be defined later, in
  -- the constructor, which glues actions together - `Bind`.
  --
  -- Finally, argument of state function should have the type of `Open` action
  -- result just because this type determines `run` return type in `IO`:
  -- when `run` runs `Open` action it'll return `IO DoorResult`. And that is
  -- the only value available for following actions from previous actions.
  Open : DoorCmd DoorResult DoorClosed (\res => case res of
                                                  OK => DoorOpen
                                                  Jammed => DoorClosed)
  Close : DoorCmd () DoorOpen (const DoorClosed)
  RingBell : DoorCmd () DoorClosed (const DoorClosed)

  -- So, here i actually define to which value state function will be applied:
  -- as i've written earlier, final state value does not matter, but initial
  -- state value does. In other words, state function provided by an action is
  -- used _not_ to determine its final state value, but to determine _initial_
  -- state of the following action. And here, in constructor glueing actions
  -- together, i clearly write, that initial state of second action is
  -- computed based on function's argument and because `Bind` is
  -- parametrically polymorphic this means, that state function will in fact
  -- be applied to previous action's resulting value.
  Bind : DoorCmd a state1 state2_fn -> ((res : a) -> DoorCmd b (state2_fn res) state3_fn) -> DoorCmd b state1 state3_fn

  -- Pure is intresting, because it's similar to `Display` and may be defined
  -- as
  --Pure : (res : ty) -> DoorCmd ty s (const s)
  --
  -- But type used in the book allows to changing state function on the go.
  -- FIXME: Do i need this?
  Pure : (res : ty) -> DoorCmd ty (state_fn res) state_fn

  Display : String -> DoorCmd () state (const state)

namespace DoorCmd
  export
  (>>=) : DoorCmd a state1 state2_fn -> ((res : a) -> DoorCmd b (state2_fn res) state3_fn) -> DoorCmd b state1 state3_fn
  (>>=) = Bind
  export
  (>>) : DoorCmd () state1 state2_fn -> DoorCmd b (state2_fn ()) state3_fn -> DoorCmd b state1 state3_fn
  mx >> my = Bind mx (\() => my)

doorProg : DoorCmd () DoorClosed (const DoorClosed)
doorProg = do
  RingBell
  x <- Open
  case x of
       OK => do
         Display "Glad To Be Of Service"
         Close
       Jammed => do
         Display "Door Jammed"

run : Stream Bool -> DoorCmd a s fn -> IO (Stream Bool, a)
run (b::bs) Open = pure (bs, if b then OK else Jammed)
run bs Close = (bs, ) <$> pure ()
run bs RingBell = (bs, ) <$> putStrLn "Ding-dong"
run bs (Display s) = (bs, ) <$> putStrLn s
run bs (Pure x) = pure (bs, x)
run bs (Bind mx f) = do
  (bs', x) <- run bs mx
  run bs' (f x)

stateFn1 : Nat -> DoorState
stateFn1 2 = DoorOpen
stateFn1 3 = DoorOpen
stateFn1 _ = DoorClosed

-- Such type
--      testPure : DoorCmd Int DoorOpen stateFn1
-- redefines `stateFn1`, so i should use instead:
testPure : DoorCmd Nat DoorOpen (\x => stateFn1 x)
testPure = Bind (Pure 2 {state_fn = stateFn1})
                (\x =>
                  case x of
                       2 => Pure 3
                       v => Pure v
                  )

testPure2 : DoorCmd () DoorOpen (const DoorClosed)
testPure2 = do
  x <- Pure 2 {state_fn = stateFn1}
  case x of
            2 => Close
            3 => do
              Close
              Display "b"
            -- I need here something, which has initial state `stateFn1 v`
            -- and output state `const DoorClosed`, but there's no such
            -- constructor: `Pure` always preserves state function, but here i
            -- need to change it. Others have specific initial state and i
            -- can't prove, that it matches with `stateFn1 v`. For the same
            -- reason `Display` won't work: i can't prove, that `stateFn1 v`
            -- equals to `DoorClosed` (though, in fact it does).
            v => ?impossible_a3 --Display "c"

logOpen : DoorCmd DoorResult DoorClosed (\res => case res of OK => DoorOpen; Jammed => DoorClosed)
logOpen = do
  Display "Trying to open the door"
  OK <- Open | Jammed => do Display "Jammed"
                            Pure Jammed
  Display "Success"
  Pure OK

data PinResult = Wrong | Correct

--data ATMCmd : (ty : Type) -> List ATMState -> (ty -> List ATMState) -> Type where
--  InsertCard : ATMCmd () [Ready] (const [CardPresent])
--  InputPin : ATMCmd PinResult [CardPresent, WrongPin]
--                        (\r => case r of
--                                    Wrong => [WrongPin]
--                                    Correct => [Session]
--                                )
--  Dispense : ATMCmd () [Session] (const [Session])
--
--  PureATM : (a : ty) -> ATMCmd ty (f a) f
--  BindATM : ATMCmd a s1 f1 -> ((r : a) -> ATMCmd b (f1 r) f2) -> ATMCmd b s1 f2

{-
data ATMState = Ready | CardPresent | WrongPin Nat | Session | CardLocked

pinRetry : PinResult -> Nat -> ATMState
pinRetry Wrong Z = WrongPin 1
pinRetry Wrong 1 = WrongPin 2
pinRetry Wrong 2 = WrongPin 3
pinRetry Wrong (S _) = CardLocked
pinRetry Correct _ = Session

data ATMCmd : (ty : Type) -> ATMState -> (ty -> ATMState) -> Type where
  InsertCard : ATMCmd () Ready (const CardPresent)
  InputPin : ATMCmd PinResult CardPresent
                        (\r => case r of
                                    Wrong => WrongPin 1
                                    Correct => Session
                              )
  BadPin : {n : Nat} -> ATMCmd PinResult (WrongPin n) (\r => pinRetry r n)
  Dispense : ATMCmd () Session (const Session)

  PureATM : (a : ty) -> ATMCmd ty (f a) f
  BindATM : ATMCmd a s1 f1 -> ((r : a) -> ATMCmd b (f1 r) f2) -> ATMCmd b s1 f2
  -}

-- FIXME: With such definition max retries may be changed during operation.
-- May be i should move it to type `ATMState maxRetries`, so it'll be
-- constant?
data ATMState = Ready
              | PinAttempts (Fin maxRetries) -- CardInserted
              | Session

--pinRetry : PinResult -> (attemptsLeft : Fin n) -> ATMState
--pinRetry Wrong FZ = CardLocked
--pinRetry Wrong (FS k) = PinAttempts k
--pinRetry Correct _ = Session

pinRetry : {0 n : Nat} -> PinResult -> (attemptsLeft : Fin n) -> ATMState
pinRetry Wrong FZ = PinAttempts {maxRetries = n} FZ
pinRetry Wrong (FS k) = PinAttempts (weaken k)
pinRetry Correct _ = Session

PIN : Type
PIN = Vect 4 Nat

data ATMCmd : (ty : Type) -> ATMState -> (ty -> ATMState) -> Type where
  -- Allow 3 attempts.
  -- FIXME: If i add maxRetries to `ATMState`, it'll probably be inferred more
  -- seamlessly.
  InsertCard : ATMCmd () Ready (const (PinAttempts {maxRetries = 4} 3))
  EjectCard : ATMCmd () s (const Ready)
  GetPin : ATMCmd PIN (PinAttempts left) (const (PinAttempts left))
  CheckPin : {0 leftAttempts : Fin n} -> PIN
              -> ATMCmd PinResult (PinAttempts (FS leftAttempts))
                              (\res => case res of
                                            Wrong => PinAttempts (weaken leftAttempts)
                                            Correct => Session)
  GetAmount : ATMCmd Nat s (const s)
  -- FIXME: Check that i have enough money.
  Dispense : Nat -> ATMCmd () Session (const Session)
  Message : String -> ATMCmd () s (const s)

  PureATM : (a : ty) -> ATMCmd ty (f a) f
  BindATM : ATMCmd a s1 f1 -> ((r : a) -> ATMCmd b (f1 r) f2) -> ATMCmd b s1 f2

namespace ATMCmd
  export
  (>>=) : ATMCmd a s1 f1 -> ((r : a) -> ATMCmd b (f1 r) f2) -> ATMCmd b s1 f2
  (>>=) = BindATM

  export
  (>>) : ATMCmd () s1 f1 -> ATMCmd b (f1 ()) f2 -> ATMCmd b s1 f2
  mx >> my = BindATM mx (\() => my)

--g {n = .(S (S n'))} (FS FZ) = g {n = (S n')} FZ
--g {n = .(S (S n'))} (FS (FS k)) = ?a2 -- g {n} (FS (weaken k))

0 foo : (x : Maybe a) -> IsJust x -> a
foo (Just x) ItIsJust = x

total
finToNatWeakNeutral : (t : Fin n) -> finToNat (weaken t) = finToNat t
finToNatWeakNeutral FZ = Refl
finToNatWeakNeutral (FS t') = cong S (finToNatWeakNeutral t')

total
atm2 : {left : Fin n} -> {l : Nat} -> {auto prf : l = finToNat left} -> ATMCmd () (PinAttempts left) (const Ready)
atm2 {left = FZ} {l = Z} = do
  Message "No retries left."
  EjectCard
atm2 {left = FS k} {l = S l'} {prf} = do
  pin <- GetPin
  r <- CheckPin pin
  case r of
       Correct => do
         Message "Pin successfull."
         sum <- GetAmount
         Dispense sum
         EjectCard
       Wrong => do
         Message "Wrong pin."
         let r = atm2 {left = weaken k} {l = l'}
                      {prf = rewrite (injective prf) in
                             rewrite (finToNatWeakNeutral k) in
                                     Refl}
         r

total
atm : ATMCmd () Ready (const Ready)
atm = do
  InsertCard
  atm2 {left = 3} {l = 3}

readPin : (n : Nat) -> Vect m Nat -> IO (Vect (n+m) Nat)
-- I'll save pin in reverse, as i read it. And reverse only once at the
-- end.
readPin Z pin = do
  _ <- getLine
  pure pin
readPin (S n') pin = do
  c <- getChar
  if isDigit c
     then rewrite plusSuccRightSucc n' m in readPin n' (pin `snoc` (cast c `minus` 48))
     else ?b1 --readPin n' pin

partial
-- Note, that states do not matter here, in `run`. Only result does. States
-- are for type-checking sequences of `ATMCmd` actions and here, when running
-- `ATMCmd` actions, states are not relevant at all (not needed and not used).
runATMCmd : (correctPin : PIN) -> ATMCmd a s f -> IO a
runATMCmd _ InsertCard = do
  putStrLn "Please insert your card (press enter)"
  x <- getLine
  pure ()
runATMCmd _ EjectCard = putStrLn "Card ejected"
-- This number comes from `PIN` type. And changing it there, won't typecheck
-- here and vice versa.
runATMCmd _ GetPin = do
    putStr "Enter PIN: "
    readPin 4 []
runATMCmd correctPin (CheckPin pin) = do
  if pin == correctPin
     then pure Correct
     else pure Wrong
runATMCmd _ GetAmount = do
  putStr "How much would you like? "
  am <- getLine
  pure (cast am)
runATMCmd _ (Dispense amount) = putStrLn ("Grab your " ++ show amount ++ " money and go away!")
runATMCmd _ (Message msg) = putStrLn msg
runATMCmd _ (PureATM x) = pure x
runATMCmd correctPin (BindATM mx f) = do
  x <- runATMCmd correctPin mx
  runATMCmd correctPin (f x)
