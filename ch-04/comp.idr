
-- Consider example.
data T : Nat -> Type where
  MkT : (n : Nat) -> T n

mylen : {1 n : Nat} -> T n -> Nat
mylen _ = n

data T' : Type where
  MkT' : (n : Nat) -> T n -> T'

mylen' : T' -> Nat
mylen' (MkT' n x) = mylen x

unwrap : (a : T') -> T (mylen' a)
unwrap (MkT' _ x) = x

unwrap2 : T' -> T 3

-- Then a function
f : (a : T') -> Nat
--
-- Can only be written as
--f x = mylen {n = mylen' x} (unwrap x)
--
-- And it doesn't compile, when written in point-free:
--f = mylen . unwrap
--
-- This may be better seen, if implicit arguments are specified manually;
--f x = (.) {b = T (mylen' x)} (mylen) unwrap $ x
--f x = (.) (mylen {n = mylen' x}) unwrap $ x

-- Regular composition.
comp : {a, b, c : Type} -> (f : b -> c) -> (g : a -> b) -> a -> c
comp f g x = f (g x)

-- This doesn't differ from regular composition, in fact. Just 'b t' is used
-- here instead of just 'b' there. Which probably also causes 'b' to become
-- non-derivable, i need to specify it manually
--
--      comp2 {b = T} mylen unwrap2
--
-- But the problem with `mylen . unwrap` is not that type 'b' should be equal
-- in both 'f' and 'g' (it already does), but that type 'b' depends from the
-- same value 'x : a' as can be seen from
--
--      f x = (.) (mylen {n = mylen' x}) unwrap $ x
comp2 : {t : k} -> {b : k -> Type}
        -> (f : b t -> c) -> (g : a -> b t) -> a -> c
comp2 f g x = f (g x)

-- Such function can't be implemented. Here 'f' needs an argument of type 'b t',
-- where 't' is defined at upper level. But 'g x' has type 'h x', which may not
-- match with already defined 't'.
comp3 : {t : k}
        -> {h : a -> k}
        -> {b : k -> Type}
        -> (f : b t -> c)
        -> (g : (y : a) -> b (h y)) -- 'h y' may not match with 't'.
        -> (x : a)
        -> c
comp3 f g x = let z = g x in ?c

-- Works, but 'b' should be specified manually (which may mean, that smth
-- unneccessary was used) as
--
--      comp4 {b = T} mylen unwrap
--
-- and i may simplify it. See below for correct answer.
comp4 : {h : a -> k}
        -> {b : k -> Type}
        -> (f : {x : a} -> b (h x) -> c)
        -> (g : (y : a) -> b (h y))
        -> (x : a)
        -> c
comp4 f g x = f (g x)

-- Works, but 'b' should be specified manually (which may mean, that smth
-- unneccessary was used) as
--
--      comp5 {b = T} mylen unwrap
--
-- The correct answer is below.
comp5 : {h : a -> k}
        -> {b : k -> Type}
        -> (f : {y : k} -> b y -> c)
        -> (g : (x : a) -> b (h x))
        -> a -> c
comp5 f g x = let z = g x in f {y = h x} z

-- Missed dependency between 'x' and 'b t' in 'g'. I can't derive 't' at upper
-- level, if it depends from value of the first argument of 'g' (i.e. from 'x').
comp5' : {b : k -> Type}
        -> {t : k}
        -> (f : {y : k} -> b y -> c)
        -> (g : (x : a) -> b t)   -- Missed dep between 'x' and 'b t'.
        -> a -> c
comp5' f g x = let z = g x in f {y = t} z

-- Working variant.
--
-- So considering the case of
--
--      comp5'2 mylen unwrap
--
-- the key point here is that idris should derive such a 'b', that:
--
--  * it takes T' as input
--  * outputs 'T ?n',
--
-- where (?n : Nat), because 'b y' is first argument of 'mylen' and should
-- have type 'T ?n'. I.e. 'b' should have the form
--
--      b = \y : T' => T ?n
--
-- And there is only one solution here: (b = \y : T' => T (mylen' y)) and then
-- (?n = mylen' y).
--
-- Why 'b' should take input of type 'a'? Well, that's because the simplest
-- way to describe dependency between arg type and result type in 'g' is to
-- take 'b : a -> Type'. And then 'f' should also take 'b' of such type.
comp5'2 : {b : a -> Type}
      -> (f : {y : a} -> b y -> c)  -- 'y' is of type 'a'!
      -> (g : (x : a) -> b x)   -- Dependency between 'x' and 'b x' is here.
      -> a -> c
comp5'2 f g x = let z = g x in f {y = x} z




-- Reference solution.
(*) : forall b. ({x : a} -> b x -> c) -> (f : (x : a) -> b x) -> a -> c
(*) g f x = g (f x)

--f : T' -> Nat
--f = mylen * unwrap
