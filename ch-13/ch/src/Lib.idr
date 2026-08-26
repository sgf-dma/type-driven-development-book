module Lib

import Data.String

%default total


data DoorState = DoorOpen | DoorClosed

-- My version of DoorCmd.
data DoorCmd2 : Type -> DoorState -> Type where
  Open2 : DoorCmd2 a DoorClosed -> DoorCmd2 a DoorOpen
  Close2 : DoorCmd2 a DoorOpen -> DoorCmd2 a DoorClosed
  RingBell2 : DoorCmd2 a DoorClosed -> DoorCmd2 a DoorClosed

  Pure2 : a -> DoorCmd2 b s1 -> DoorCmd2 a s1
  Bind2 : DoorCmd2 a s1 -> (a -> DoorCmd2 b s2) -> DoorCmd2 b s2

doorProg2 : DoorCmd2 () DoorClosed -> DoorCmd2 () DoorClosed
doorProg2 = Close2 . Open2 . RingBell2

data DoorCmd : Type -> DoorState -> DoorState -> Type where
  Open : DoorCmd () DoorClosed DoorOpen
  Close : DoorCmd () DoorOpen DoorClosed
  RingBell : DoorCmd () DoorClosed DoorClosed

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
  Close

VendState : Type
VendState = (Nat, Nat)

data Input = COIN
           | VEND
           | CHANGE
           | REFILL Nat

data MachineCmd : Type -> VendState -> VendState -> Type where
  InsertCoin : MachineCmd () (p, c) (S p, c)
  Vend : MachineCmd () (S p, S c) (p, c)
  GetCoins : MachineCmd () (p, c) (Z, c)

  Refill :(bars : Nat) -> MachineCmd () (Z, chocs) (Z, bars + chocs)
  --Rff :(bars : Nat) -> MachineCmd () (p, chocs) (p, bars + chocs)
  Display : String -> MachineCmd () (p, c) (p, c)
  GetInput : MachineCmd (Maybe Input) state state

  PureCmd : ty -> MachineCmd ty state state
  BindCmd : MachineCmd a state1 state2 -> (a -> MachineCmd b state2 state3) -> MachineCmd b state1 state3

ha : MachineCmd () (p, c) (S p, c)
ha = BindCmd (Display "A") (\_ => InsertCoin)

hb : MachineCmd () (p, c) (S p, c)
hb = BindCmd GetInput (\ms =>
        BindCmd (maybe (Display "A") (\s => Display "B") ms) (\_ => InsertCoin))

namespace MachineCmd
  export
  (>>=) : MachineCmd a state1 state2 -> (a -> MachineCmd b state2 state3) -> MachineCmd b state1 state3
  (>>=) = BindCmd
  export
  (>>) : MachineCmd () state1 state2 -> MachineCmd b state2 state3 -> MachineCmd b state1 state3
  mx >> my = mx >>= \_ => my

-- Note, that i don't need to pass state at value level at all! It's
-- completely passed at type-level and, moreover, at compile-time only: all
-- state arguments has multiplicity 0 and are erased at runtime!
run : MachineCmd a s1 s2 -> IO a
run InsertCoin = pure ()
run Vend = pure ()
run GetCoins = pure ()
run (Refill bars) = pure ()
run (Display str) = putStrLn str
run GetInput = do
  putStr "> "
  inp <- getLine
  case words inp of
       ["coin"] => pure (Just COIN)
       ["vend"] => pure (Just VEND)
       ["change"] => pure (Just CHANGE)
       ["refill", n] => pure (Just (REFILL (cast {to = Nat} n)))
       _ => pure Nothing
run (PureCmd x) = pure x
run (BindCmd mx cont) = run mx >>= run . cont

data MachineIO : VendState -> Type where
  Do : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1

data Fuel : Type where
  Dry : Fuel
  More : Lazy Fuel -> Fuel

partial
forever : Fuel
forever = More forever

total
runIO : Fuel -> MachineIO s1 -> IO ()
runIO Dry _ = pure ()
runIO (More fuel) (Do cmd cont) = do
  x <- run cmd
  runIO fuel (cont x)

namespace MachineIO
  export
  (>>=) : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1
  (>>=) = Do
  export
  (>>) : MachineCmd a state1 state2 -> Inf (MachineIO state2) -> MachineIO state1
  mx >> my = mx >>= \_ => my
  --mx >> my = Do mx (\_ => my)

loop : {pounds, chocs : Nat} -> MachineIO (pounds, chocs)
-- If i use `state3` as resulting type of `MachineIO.Do`, than `p` and `c` in
-- initial `InsertCoin` state can't be deduced from entire `loop` type
-- and i need to specify initial state manually:
--loop = Do (InsertCoin {p = pounds} {c = chocs}) (\_ => loop)
-- On the other hand, if i use `state1` as final state (which will never be
-- reached anyway, because MachineIO type's values are always infinite) type
-- checker will be able to deduce initial state for first operation from
-- _final_ state.
loop = Do InsertCoin (\_ => loop)

mutual
  -- I can't implement `vend` in MachineCmd (not in its current form at least)
  -- (i.e. to avoid calling `machineLoop` from `vend` directly), like
  --
  --    vend  : {pounds, chocs : Nat} -> MachineCmd ...
  --
  -- because `Vend` and `Display` have different _final state_: `Vend`
  -- reduces number of pounds and chocs, but Display does not change.
  -- Therefore, to place both this operations into single function, i should
  -- either not include final state in type at all or somehow revert state
  -- back. Reverting state has no sense, but ignoring final state is exactly
  -- what MachineIO's `Do` does: it takes infinite continuation with
  -- state2, but entire computation still has state1 in type. So, here
  -- `machineLoop` calls in different cases have _different_ types, because
  -- state2 differs, but entire branch still has the same type, because only
  -- state1 matters in MachineIO. And state1 is in fact `(pounds, chocs)`.
  -- Different state1 requirments for operations of MachineCmd is not a
  -- problem and handled by simple pattern matching. Therefore, in `Vend` case
  -- state1 will be `(S pounds', S chocs')`, but in `Display` case it'll be
  -- just `(Z, chocs)` or `(pounds, Z)` respectively.
  total
  vend : {pounds, chocs : Nat} -> Inf (MachineIO (pounds, chocs))
  vend {pounds = S pounds'} {chocs = S chocs'} = do
    Vend
    Display $ "Coins left: " ++ show pounds' ++ ", chocs left: " ++ show chocs'
    machineLoop
  vend {pounds = Z } = do
    Display "Insert a coin"
    machineLoop
  vend {chocs = Z } = do
    Display "Out of stock"
    machineLoop

  total
  refill : {pounds, chocs : Nat} -> (bars : Nat) -> Inf (MachineIO (pounds, chocs))
  refill {pounds = Z} {chocs} bars = do
    Refill bars
    Display $ "Current chocs: " ++ show (bars + chocs)
    machineLoop
  refill {pounds = S _} _ = do
    Display "Get back coins first before refilling"
    machineLoop

  total
  machineLoop : {pounds, chocs : Nat} -> (MachineIO (pounds, chocs))
  machineLoop = do
    mi <- GetInput
    case mi of
         Just COIN => do
           InsertCoin
           Display $ "Current balance: " ++ show (pounds + 1)
           -- I can't move `machineLoop` out of case (call it after case) for
           -- the same reason as was written above for `vend`: these
           -- `machineLoop` calls have _different_ types in _different_ case
           -- branches (`pounds` and `chocs` in `machineLoop` type are forall
           -- type variables), because state2 of preceding operation differs.
           -- But if i move `machineLoop` after the case, i need for
           -- all case branches to be of the same `MachineCmd` type, which is
           -- impossible, because though operations are of type `MachineCmd`,
           -- their types are different due to state.
           machineLoop
         Just VEND => vend
         Just CHANGE => do
            GetCoins
            Display $ "Returned " ++ show pounds ++ " coins"
            machineLoop
         Just (REFILL bars) => refill bars
         Nothing => do
           Display "Wrong command"
           machineLoop

data MachineCmd2 : Type -> VendState -> Type where
  -- It's probably better to have constructors of type
  --
  --    MachineCmd2 a (p, c) -> MachineCmd2 () (S p, c)
  --
  -- but that'll result in unsolved holes, when using MachineCmd2 with
  -- MachineIO2's `Comp`: if i can define `>>' as it should be with argument
  -- of type `m ()`, everything would probably work, but Idris thinks then,
  -- that all functions using `>>` are not total, therefore i may only use
  -- `m a` as first argument. And with `m a` type `a` can't be derived in `>>`
  -- and need to be specified manually each time. The one solution to this is
  -- to make type more strict here, in MachineCmd2 itself.
  InsertCoin2 : MachineCmd2 a (p, c) -> MachineCmd2 () (S p, c)
  Vend2 : MachineCmd2 a (S p, S c) -> MachineCmd2 () (p, c)
  GetCoins2 : MachineCmd2 a (p, c) -> MachineCmd2 () (Z, c)

  Refill2 : (bars : Nat) -> MachineCmd2 a (Z, c) -> MachineCmd2 () (Z, bars + c)
  Display2 : String -> MachineCmd2 a (p, c) -> MachineCmd2 () (p, c)
  -- type parameter 'a' in resulting type determines result type in IO in
  -- `run2`.
  GetInput2 : MachineCmd2 a (p, c) -> MachineCmd2 (Maybe Input) (p, c)
  -- 'BindCmd' gives the ability to pass the value obtained during running
  -- some operation denoted by 'mx' constructor into subsequent operation.
  -- I.e. to use the value of current operation somewhere further. Without
  -- similar construction allowing to specify function _taking the result of
  -- current operation_ i can't achieve this.
  -- Correct definition of 'Func' is this, however it doesn't compile, because
  -- Idris will think, that such constructor have types not in positive
  -- position, which is wrong, i think.
  --Func : (a -> MachineCmd2 d (p0, c0) -> MachineCmd2 b (p, c)) ->
  --       MachineCmd2 a (p0, c0) -> MachineCmd2 b (p, c)
  -- Anyway, i may use following definition, which should also work, but
  -- function must be reduced to single value by applying to `Start2` (see
  -- below)
  Func : (a -> MachineCmd2 b (p, c)) -> MachineCmd2 a (p0, c0) -> MachineCmd2 b (p, c)

  -- State should be written as `s`, otherwise `(p, c)` and `s` types won't
  -- unify in `runIO2` by some reason..
  Start2 : MachineCmd2 () s

total
ttt : Maybe Int -> MachineCmd2 () (p, c) -> MachineCmd2 () (p, c)
ttt ms = maybe (Display2 "A") (\s => Display2 "B") ms

-- The first difference of v2 and v1 versions of MachineCmd is how value is
-- built: there (in v1) MachineCmd value is built using `BindCmd`. Therefore,
-- current action is first argument of BindCmd and further actions are
-- embedded into the continuation function (second argument of BindCmd). That
-- means, when unwrapping BindCmd value, first action is in the topmost
-- BindCmd constructor. Here (in v2) all is reverse: because i use function
-- composition `f (g x)`, first action `g` will be the last. In other words,
-- here constructor denoting the last action takes all actions, which had
-- occured before, as argument.
ha2 : MachineCmd2 () (p, c) -> MachineCmd2 () (S p, c)
ha2 = InsertCoin2 . Display2 "A"
--ha2 = InsertCoin2 (Display2 "A")

-- The second difference is how to use result of previous computation. There
-- (in v1) BindCmd constructor's second argument is function taking result of
-- first action, and when `run` executes (in IO) actions denoted by BindCmd's
-- first argument and returns result, that result may be directly passed to
-- the BindCmd's second argument (function) to obtain another MachineCmd
-- action, which will be evaluated (see `run`):
--
--      run (BindCmd mx cont) = run mx >>= run . cont
--
-- Here (in v2) i can't do this directly, because regular constructors just
-- wraps previous MachineCmd values, but does not provide any function of type
-- `a -> MachineCmd ..`, which may use result of previous action. Therefore, i
-- need a special constructor similar to `BindCmd`, which will take both
-- previous actions as single MachineCmd value _and_ a function, which may use
-- the result of previous actions.
--
--      Func : (a -> MachineCmd2 b (p, c)) -> MachineCmd2 a (p0, c0) -> MachineCmd2 b (p, c)
--             ...                                        |
--              ^-----------------------------------------+
--
-- but to be able to use composition of MachineCmd values also for building
-- this continuation function, i need it to have type
--
--      a -> MachineCmd2 x (p0, c0) -> MachineCmd2 b (p, c)
--
-- but unfortunately Idris thinks, that constructor of type
--
--      MkT : (a -> T -> T) -> T
--
-- has T (the type been defined) in negative position, so it's not possible to
-- define such constructor. So, to define function for use in `Func` i need to
-- apply regular MachineCmd2 value composition to `Start2` special value.
hb2 : MachineCmd2 () (p, c) -> MachineCmd2 () (S p, c)
hb2 = Func (\ms => InsertCoin2 . (maybe (Display2 "A") (\s => Display2 "B") ms) $ Start2)
        . GetInput2

run2 : MachineCmd2 a s1 -> IO a
-- In v1 `run` i specify only actions required by the exact constructor _as it
-- would have been alone_ for all constructors, _except_ `BindCmd`, but here i
-- have recursive calls in _each_ branch. This is because in v1 only `BindCmd`
-- is actually used for building a chain of actions, but in v2 any constructor
-- may chain to another by itself.
run2 (InsertCoin2 x) = do
  -- Here InsertCoin2 is the last action wrapping previous actions as its
  -- argument, therefore, unlike v1 BindCmd's `run` branch, here i first
  -- execute `x`.
  _ <- run2 x
  pure ()
run2 (Vend2 x) = do
  _ <- run2 x
  pure ()
run2 (GetCoins2 x) = do
  _ <- run2 x
  pure ()
run2 (Refill2 bars x) = do
  _ <- run2 x
  pure ()
run2 (Display2 str x) = do
  _ <- run2 x
  putStrLn str
  pure ()
run2 (GetInput2 x) = do
  putStr "> "
  _ <- run2 x
  inp <- getLine
  case words inp of
       ["coin"] => pure (Just COIN)
       ["vend"] => pure (Just VEND)
       ["change"] => pure (Just CHANGE)
       ["refill", n] => pure (Just (REFILL (cast {to = Nat} n)))
       _ => pure Nothing
run2 Start2 = pure ()
-- Note, that `Func` branch is exactly the same as `BindCmd` of v1.
run2 (Func cont x) = run2 x >>= run2 . cont

data MachineIO2 : VendState -> Type where
  -- Correct definition seems to be this:
  --Comp : (MachineCmd2 a s1 -> MachineCmd2 b s2) -> (b -> Inf (MachineIO2 s2)) -> MachineIO2 s1
  -- but then type 'a' can't be derived and need to be specified manually each
  -- time. So, i make it more strcit:
  Comp : (MachineCmd2 () s1 -> MachineCmd2 a s2) -> (a -> Inf (MachineIO2 s2)) -> MachineIO2 s1

namespace MachineIO2
  export
  (>>=) : (MachineCmd2 () s1 -> MachineCmd2 a s2) -> (a -> Inf (MachineIO2 s2)) -> MachineIO2 s1
  (>>=) = Comp
  export
  (>>) : (MachineCmd2 () s1 -> MachineCmd2 a s2) -> Inf (MachineIO2 s2) -> MachineIO2 s1
  --mx >> my = mx >>= \_ => my
  mx >> my = Comp mx (\_ => my)

total
runIO2 : Fuel -> MachineIO2 s1 -> IO ()
runIO2 Dry _ = pure ()
runIO2 (More fuel) (Comp h cont) = do
  x <- run2 (h Start2)
  runIO2 fuel (cont x)

-- And here note, that _all_ other code is _absolutely_ the same as was in v1!
total
loop2 : MachineIO2 (pounds, chocs)
--loop2 = Comp InsertCoin2 (\_ => loop2)
loop2 = do
  InsertCoin2
  loop2

-- Note, that in fact i may get rid of both `BindCmd` (in v1) and `Func` (in v2)
-- constructors at all, because i have `MachineIO` and i may use its `Do` or
-- `Comp` respectively, when i need to use result of previous `MachineCmd`
-- computation. Moreover, as following  program demonstrates, that's indeed
-- all i need: neither in v1, nor here i don't use `BindCmd` or `Func`! All
-- `do` actions occur inside `MachineIO`, i.e. having `MachineIO` i don't need
-- to chain individual `MachineCmd` actions in `MachineCmd`, i may just chain
-- them in `MachineIO` directly.
mutual
  total
  vend2 : {pounds, chocs : Nat} -> Inf (MachineIO2 (pounds, chocs))
  vend2 {pounds = S pounds'} {chocs = S chocs'} = do
    Vend2
    Display2 $ "(2) Coins left: " ++ show pounds' ++ ", chocs left: " ++ show chocs'
    machineLoop2
  vend2 {pounds = Z } = do
    Display2 "(2) Insert a coin"
    machineLoop2
  vend2 {chocs = Z } = do
    Display2 "(2) Out of stock"
    machineLoop2

  total
  refill2 : {pounds, chocs : Nat} -> (bars : Nat) -> Inf (MachineIO2 (pounds, chocs))
  refill2 {pounds = Z} {chocs} bars = do
    Refill2 bars
    Display2 $ "(2) Current chocs: " ++ show (bars + chocs)
    machineLoop2
  refill2 {pounds = S _} _ = do
    Display2 "(2) Get back coins first before refilling"
    machineLoop2

  total
  machineLoop2 : {pounds, chocs : Nat} -> (MachineIO2 (pounds, chocs))
  machineLoop2 = do
    mi <- GetInput2
    case mi of
         Just COIN => do
           InsertCoin2
           Display2 ("(2) Current balance: " ++ show (pounds + 1))
           machineLoop2
         Just VEND => vend2
         Just CHANGE => do
            GetCoins2
            Display2 ("(2) Returned " ++ show pounds ++ " coins")
            machineLoop2
         Just (REFILL bars) => refill2 bars
         Nothing => do
           Display2 "(2) Wrong command"
           machineLoop2

