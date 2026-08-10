module Lib

import Control.Monad.State


data MyState : (stateType : Type) -> Type -> Type where
  Get : MyState stateType stateType
  Put : stateType -> MyState stateType ()
  Pure : ty -> MyState stateType ty
  Bind : MyState stateType a -> (a -> MyState stateType b) -> MyState stateType b

runMyState : s -> MyState s a -> (s, a)
runMyState s0 Get = (s0, s0)
runMyState s0 (Put s1) = (s1, ())
runMyState s0 (Pure x) = (s0, x)
runMyState s0 (Bind mx f) = let (s1, x) = runMyState s0 mx in runMyState s1 (f x)

Functor (MyState s) where
  map f mx = Bind mx (\x => Pure (f x))

Applicative (MyState s) where
  pure = Pure
  mf <*> mx = Bind mf (\f => Bind mx (\x => Pure (f x)))

Monad (MyState s) where
  (>>=) = Bind


-- The old Haskell implementation.
data MyState2 : (stateType : Type) -> Type -> Type where
  MkMyState2 : (stateType -> (stateType, a)) -> MyState2 stateType a

runMyState2 : s -> MyState2 s a -> (s, a)
runMyState2 s0 (MkMyState2 h) = h s0

getMy2 : MyState2 s s
getMy2 = MkMyState2 (\s => (s, s))

putMy2 : s -> MyState2 s ()
putMy2 s1 = MkMyState2 (\_ => (s1, ()))

pureMy2 : a -> MyState2 s a
pureMy2 x = MkMyState2 (\s => (s, x))

bindMy2 : MyState2 s a -> (a -> MyState2 s b) -> MyState2 s b
bindMy2 (MkMyState2 h) f = MkMyState2 $ \s0 => let (s1, x) = h s0
                                               in  runMyState2 s1 (f x)

Functor (MyState2 s) where
  map f (MkMyState2 h) = MkMyState2 $ \s0 => let (s1, x) = h s0 in (s1, f x)

Applicative (MyState2 s) where
  pure x = MkMyState2 (\s => (s, x))
  MkMyState2 mf <*> MkMyState2 mx = MkMyState2 $ \s0 => let (s1, f) = mf s0
                                                            (s2, x) = mx s1
                                                        in  (s2, f x)

Monad (MyState2 s) where
  MkMyState2 mx >>= f = MkMyState2 $ \s0 => let (s1, x) = mx s0
                                            in  runMyState2 s1 (f x)
