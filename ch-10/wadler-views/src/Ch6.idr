
module Ch6

%default total

public export
data JoinList : Type -> Type where
  JNil : JoinList a
  JUnit : (x : a) -> JoinList a
  JJoin : (left : JoinList a) -> (right : JoinList a) -> JoinList a

export
consIn : (jxs : JoinList a) -> List a
consIn JNil = []
consIn (JUnit x) = [x]
consIn (JJoin JNil right) = consIn right
consIn (JJoin (JUnit x) right) = x :: consIn right
consIn (JJoin (JJoin ls rs) right) =
  -- Definition from the paper breaks totality check:
  --consIn (ls `JJoin` (rs `JJoin` right))
  -- I can use '++' to avoid this:
  consIn ls ++ consIn (rs `JJoin` right)

export
-- Or i can use accumulator, if '++' is not available:
consIn2 : (jxs : JoinList a) -> List a
consIn2 jxs = go jxs []
  where
    go : (jxs : JoinList a) -> (acc : List a) -> List a
    go JNil acc = acc
    go (JUnit x) acc = x::acc
    go (JJoin JNil right) acc = go right acc
    go (JJoin (JUnit x) right) acc = x :: go right acc
    go (JJoin (JJoin ls rs) right) acc =
      go ls (go (JJoin rs right) acc)

export
consOut : (xs : List a) -> JoinList a
consOut [] = JNil
consOut (x::xs') = JJoin (JUnit x) (consOut xs')

public export
data SnocL : Type -> Type where
  SNil : SnocL a
  SSnoc : SnocL a -> a -> SnocL a

export
Eq a => Eq (SnocL a) where
  SNil == SNil = True
  (SSnoc sx x) == (SSnoc sy y) = x == y && sx == sy
  _ == _ = False

export
snocIn : (jxs : JoinList a) -> SnocL a
snocIn jxs0 = go SNil jxs0
  where
    go : (acc : SnocL a) -> (jxs : JoinList a) -> SnocL a
    go acc JNil = acc
    go acc (JUnit x) = SSnoc acc x
    go acc (JJoin left JNil) = go acc left
    go acc (JJoin left (JUnit x)) = SSnoc (go acc left) x
    go acc (JJoin left (JJoin ls rs)) = go (go acc (left `JJoin` ls)) rs

export
snocOut : (sx : SnocL a) -> JoinList a
snocOut SNil = JNil
snocOut (SSnoc sx' x) = JJoin (snocOut sx') (JUnit x)
