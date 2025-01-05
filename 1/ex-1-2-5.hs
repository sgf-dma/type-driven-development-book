{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}

import GHC.Base
import qualified GHC.TypeLits as T


type Vect :: T.Nat -> Type -> Type
data Vect n a where
    Nil :: Vect 0 a
    Cons :: a -> Vect n a -> Vect (n T.+ 1) a

-- Or 'reverse' ?
ex1 :: Vect n a -> Vect n a
ex1 = id

type family TEq a b where
    TEq a a = 'True
    TEq _ _ = 'False
ex2 :: forall (n :: T.Nat) a. Vect n a -> Vect (n T.+ n) a
ex2 Nil = Nil
--ex2 xs0@(Cons _ _) = append xs0 xs0

type family TSum (n :: T.Nat) (m :: T.Nat) where
    TSum 0 m = 0 T.+ m
    TSum n m = ((n T.- 1) T.+ m) T.+ 1

class Comm a b where

instance (forall (t1 :: T.Nat) (t2 :: T.Nat) (a :: T.Nat) (b :: T.Nat) (c :: T.Nat). t1 ~ ((a T.+ b) T.+ c), t2 ~ ((a T.+ c) T.+ b)) => Comm t1 t2 where
--instance (forall t1 (t2 :: T.Nat) a b c. t1 ~ ((a T.+ b) T.+ c), t2 ~ ((a T.+ c) T.+ b)) => Comm t1 t2 where

append :: forall a (n :: T.Nat) (m :: T.Nat). Vect n a -> Vect m a -> Vect (n T.+ m) a
append Nil ys = ys
--append (Cons x xs) ys = Cons x (append xs ys)

-- tail
{-ex3 :: Vect (n T.+ 1) a -> Vect n a
ex3 Nil = Nil-}
--ex3 (Cons x xs) = xs

-- index
-- ex4 :: Lt m n => Vect n a -> a
