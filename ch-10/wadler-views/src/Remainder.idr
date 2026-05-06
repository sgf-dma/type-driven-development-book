module Remainder

import Data.Nat
import Data.List
import Data.List.Views
import Decidable.Equality
import Syntax.PreorderReasoning

%default total

lteIsEqOrLT : {m : Nat} -> (lte : n `LTE` m) -> Either (n = m) (n `LT` m)
lteIsEqOrLT LTEZero {m = Z} = Left Refl
lteIsEqOrLT LTEZero {m = S m'} = Right (LTESucc LTEZero)
lteIsEqOrLT (LTESucc lte) = case lteIsEqOrLT lte of
                              Left eq => Left (cong S eq)
                              Right lt => Right (LTESucc lt)

public export
data Remainder1 : Nat -> Nat -> Type where
  MkRem1 : {0 n, m : Nat} -> {auto 0 isS : IsSucc m} ->
           (k, r : Nat) -> {auto 0 prfN : n = k*m + r} -> {auto prfR : r `LT` m} ->
           Remainder1 n m

export
Eq (Remainder1 n m) where
  _ == _ = True

-- I may either prove by induction on first argument `n`, like in
-- findRemainder1 and findRemainder2.

export
-- The same as findRemainder2 below, but even simpler. Recurse by first
-- argument.
findRemainder1 : (n, m : Nat) -> {auto 0 isS : IsSucc m} -> Remainder1 n m
findRemainder1 Z (S m') {isS = ItIsSucc} = MkRem1 0 0 {prfR = LTESucc LTEZero}
findRemainder1 (S n') (S m') {isS = ItIsSucc} =
  let rec = findRemainder1 n' (S m')
  in case rec of
      MkRem1 k r {prfN = prfN} {prfR = prfR} =>
        case lteIsEqOrLT prfR of
                Left Refl =>
                  MkRem1 (k + 1) 0
                            {prfN = sym $ Calc $
                                          |~ (k + 1) * S r + 0
                                          ~~ (k + 1) * S r
                                                ...(plusZeroRightNeutral ((k + 1) * S r))
                                          ~~ k * (S r) + 1 * S r
                                                ...(multDistributesOverPlusLeft k 1 (S r))
                                          ~~ k * (S r) + S r
                                                ...(rewrite multOneLeftNeutral (S r) in Refl)
                                          ~~ S (k * (S r) + r)
                                                ...(sym (plusSuccRightSucc (k * S r) r))
                                          ~~ S n' ...(rewrite sym prfN in Refl)
                                      }
                            --{prfR = LTESucc LTEZero}
                Right srLTm =>
                  MkRem1 k (S r)
                            {prfN = Calc $
                                    |~ S n'
                                    ~~ S (k*(S m') + r) ...(rewrite prfN in Refl)
                                    ~~ k*(S m') + (S r) ...(rewrite plusSuccRightSucc (k*(S m')) r in Refl)
                             }
                             --{prfR = srLTm}

public export
-- I don't need 'm `LTE` n' contraint in fact, but anyway.
data Remainder2 : Nat -> Nat -> Type where
  MkRem2 : {0 n, m : Nat} -> {auto 0 isS : IsSucc m} -> {auto lte : m `LTE` n} ->
           (k, r : Nat) -> {auto 0 prfN : n = k*m + r} -> {auto prfR : r `LT` m} ->
           Remainder2 n m

export
Eq (Remainder2 n m) where
  _ == _ = True

-- The same version as above findRemainder1, but for slightly different
-- Remainder type definition. Apart from one extra case, these functions are
-- almost identical. Recurse by first argument.
export total
findRemainder2 : (n, m : Nat) -> {auto 0 isS : IsSucc m} -> {auto lte : m `LTE` n} -> Remainder2 n m
findRemainder2 Z Z {lte = LTEZero} impossible
-- I need unpack `n` to call `findRemainder2` recursively with `n`, and i
-- need to unpack `m` into `S m'` for proving `isS` of MkRem2 .
findRemainder2 (S n') (S m') {isS = ItIsSucc} {lte = lte} with (lteIsEqOrLT lte)
  findRemainder2 (S n') (S n') {lte = _} | Left Refl =
    MkRem2 1 0
                {prfN = sym $ Calc $
                         |~ S (n' + 0) + 0
                         ~~ S (n' + 0) ...(plusZeroRightNeutral (S (n' + 0)))
                         ~~ S n' ...(rewrite plusZeroRightNeutral n' in Refl)
                }
                --{prfR = LTESucc LTEZero}
  findRemainder2 (S n') (S m') {lte = lte} | Right lt =
    case lt of
      LTESucc lte' => case findRemainder2 n' (S m') {lte = lte'} of
        MkRem2 k r {prfN = prfN} {prfR = prfR} => case lteIsEqOrLT prfR of
          Left Refl =>
            MkRem2  (k + 1) 0
                    {prfN = sym $ Calc $
                                  |~ (k + 1) * S r + 0
                                  ~~ (k + 1) * S r
                                        ...(plusZeroRightNeutral ((k + 1) * S r))
                                  ~~ k * (S r) + 1 * S r
                                        ...(multDistributesOverPlusLeft k 1 (S r))
                                  ~~ k * (S r) + S r
                                        ...(rewrite multOneLeftNeutral (S r) in Refl)
                                  ~~ S (k * (S r) + r)
                                        ...(sym (plusSuccRightSucc (k * S r) r))
                                  ~~ S n' ...(rewrite sym prfN in Refl)
                              }
                    --{prfR = LTESucc LTEZero}
          Right srLTm =>
            MkRem2  k (S r)
                    {prfN = Calc $
                            |~ S n'
                            ~~ S (k*(S m') + r) ...(rewrite prfN in Refl)
                            ~~ k*(S m') + (S r) ...(rewrite plusSuccRightSucc (k*(S m')) r in Refl)
                     }
                     --{prfR = srLTm}

-- Some lemmas for following findRemainder3 .

total
minusLte : (n, m : Nat) -> {auto 0 lte : m `LTE` n} -> Nat
minusLte n Z {lte = LTEZero} = n
minusLte (S n) (S m) {lte = LTESucc lte} = minusLte n m

minusEqZero : (n, m : Nat) -> {auto lte : m `LTE` n} -> minusLte n m = 0 -> n = m
minusEqZero n Z prf = prf
minusEqZero (S n) (S m) prf {lte = LTESucc lte} = let rec = minusEqZero n m prf in cong S rec

minusEqPlus : (n, m, k : Nat) -> {auto lte : m `LTE` n} -> minusLte n m = k -> n = m + k
minusEqPlus n Z k prf = prf
minusEqPlus (S n) (S m) k prf {lte = LTESucc lte} = cong S (minusEqPlus n m k prf)

plusRightLte : {n : Nat} -> {0 m : Nat} -> (n + m) `LTE` k -> m `LTE` k
plusRightLte {n = Z} lte = lte
plusRightLte {n = S n} (LTESucc lte) = let rec = plusRightLte {n = n} lte in lteSuccRight rec

ltePred : LTE (S m) (S n) -> LTE m n
ltePred LTEZero impossible
ltePred (LTESucc lte) = lte

lteNeqIsLt : {0 n : Nat} -> {m : Nat} -> (lte : n `LTE` m) -> (0 neq : Not (n = m)) -> n `LT` m
lteNeqIsLt LTEZero neq {m = Z} = void (neq Refl)
lteNeqIsLt LTEZero neq {m = S m'} = LTESucc LTEZero
lteNeqIsLt (LTESucc lte) neq =
  let rec = lteNeqIsLt lte (\eq => neq (cong S eq))
  in LTESucc rec

-- Not used.
lteZeroEqZero : n `LTE` 0 -> n = 0
lteZeroEqZero LTEZero = Refl
lteZeroEqZero (LTESucc _) impossible

-- Even if i constrain `m` to be greater, than 0, i still can't use
-- multiplicity 0 on m, because i still need to pattern-match on it.
lteNeqIsLt' : {0 n : Nat} -> {m : Nat} -> {iss : IsSucc m} ->
              (lte : n `LTE` m) -> (0 neq : Not (n = m)) -> n `LT` m
lteNeqIsLt' LTEZero neq {m = S m'} = LTESucc LTEZero
lteNeqIsLt' (LTESucc lte) neq {m = S Z} =
  let w = lteZeroEqZero lte in void (neq (cong S w))
lteNeqIsLt' (LTESucc lte) neq {m = S (S m')} =
  let rec = lteNeqIsLt' lte (\eq => neq (cong S eq)) {iss = ItIsSucc}
  in LTESucc rec

lteSelf : {n : Nat} -> LTE n n
lteSelf {n = Z} = LTEZero
lteSelf {n = S n'} = LTESucc lteSelf

-- Or i may (instead of using induction on first argument, as in
-- findRemainder1 and findRemainder2) subtract divider from first argument
-- until result will be lesser, than divider. findRemainder3,
-- findRemainder4 and findRemainder5 implement this.

-- This is _not_ tail recursive version and it's quite complex with no real
-- benefits.
total
findRemainder3' : (n : Nat) -> {auto u : Nat} -> {auto upper : n `LTE` u} ->
     (m : Nat) -> {auto lte : S m `LTE` n} -> Remainder2 n (S m)
findRemainder3' Z Z impossible
findRemainder3' n Z = MkRem2 n 0 {prfN = Calc $
                              |~ n
                              ~~ n * 1 ...(sym (multOneRightNeutral n))
                              ~~ (n * 1) + 0 ...(sym (plusZeroRightNeutral (n * 1)))
                            }
findRemainder3' n m {u = S u'} with (minusLte n (S m)) proof 0 minusPrf
  -- The same as `findRemainder2 (S n') (S n')` branch, except that i don't
  -- need `minusEqZero` there, because `lteIsEqOrLT` already provides equality
  -- proof. I can use it here too by the way.
  _ | Z = MkRem2 1 0 {prfN = Calc $
                              |~ n
                              ~~ S m ...(minusEqZero n (S m) minusPrf)
                              ~~ S (m + 0) ...(sym (plusZeroRightNeutral (S m)))
                              ~~ S ((m + 0) + 0) ...(sym (plusZeroRightNeutral (S (m + 0)))) }
                    --{prfR = LTESucc LTEZero}

  _ | (S r) = case decEq (S m) (S r) of
      -- The same as `lteIsEqOrLT prfR of Left Refl` branch in
      -- `findRemainder2`, i.e. when (remainder + 1) equals to divider. There i
      -- also unpack `n` to `S n'`, but here i don't need this.
      Yes smEqSr => MkRem2 2 0
                      { prfN = Calc $
                              |~ n
                              ~~ S m + S r ...(minusEqPlus n (S m) (S r) minusPrf)
                              ~~ S m + S m ...(rewrite smEqSr in Refl)
                              ~~ S (m + S m) + 0
                                      ...(rewrite sym (plusZeroRightNeutral (S m + S m)) in Refl)
                              ~~ S m + (S m + 0) + 0
                                      ...(rewrite plusZeroRightNeutral (S m) in Refl)
                            }
                    --{prfR = LTESucc LTEZero}

      No smNeqSr => case connex smNeqSr {rel = LTE} of
        -- I don't have this `Left` branch in `findRemainder2` at all, because
        -- there i use recursive call to `findRemainder2` itself and it returns
        -- proper remainder, which is lesser, than divider. Here, on the other
        -- hand, i use subtraction and the "remainder" may be _either greater
        -- or lesser_, than divider. If remainder is greater, i need to
        -- recurse further and i need decreasing upper bound to preserve
        -- totality in this recursion.
        Left smLteSr =>
          let upPrf : S (m + (S r)) `LTE` S u'
              upPrf = rewrite sym (minusEqPlus n (S m) (S r) minusPrf) in upper
              rec = findRemainder3' (S r) {u = u'} m {upper = plusRightLte (ltePred upPrf)} {lte = smLteSr}
          in case rec of
              MkRem2 k r2 {prfN = prfN} =>
                MkRem2 (k+1) r2
                      {prfN = sym $ Calc $
                          |~ (k + 1) * S m + r2
                          ~~ (k * S m + 1 * S m) + r2
                                ...(rewrite multDistributesOverPlusLeft k 1 (S m) in Refl)
                          ~~ (k * S m + S m) + r2
                                ...(rewrite multOneLeftNeutral (S m) in Refl)
                          ~~ (S m + k * S m) + r2
                                ...(rewrite plusCommutative (k * S m) (S m) in Refl)
                          ~~ S m + (k * S m + r2)
                                ...(rewrite sym (plusAssociative (S m) (k * S m) r2) in Refl)
                          ~~ S m + S r ...(rewrite prfN in Refl)
                          ~~ n ...(sym (minusEqPlus n (S m) (S r) minusPrf))
                        }

        -- This branch is the same as `Right srLTm` branch in `findRemainder2`.
        -- Note, that here i don't have `prfR` prove readily available.
        Right srLteSm =>
          MkRem2  1 (S r)
                  {prfN = Calc $
                            |~ n
                            ~~ S m + S r ...(minusEqPlus n (S m) (S r) minusPrf)
                            ~~ S ((m + 0) + S r)
                                  ...(rewrite sym (plusZeroRightNeutral m) in Refl)
                        }
                  -- In fact, i may avoid using `lteNeqIsLt` here if i'll use
                  -- something better, than `decEq` followed by `connex {rel = LTE}`,
                  -- because i have enough data to prove 'S r `LT` S m'
                  -- directly, but `connex` can't be called for `LT`.
                  {prfR = lteNeqIsLt srLteSm (\srNeqSm => smNeqSr (sym srNeqSm))}

export
findRemainder3 : (n, m : Nat) -> {auto 0 isS : IsSucc m} -> {auto lte : m `LTE` n} ->
                                  Remainder2 n m
findRemainder3 n (S m') {lte = lte} = findRemainder3' n m' {u = n} {upper = lteSelf}

-- This definition is wrong, because i need remainder to be strictly lesser,
-- than divider. Also, constraint `lte` is superfluous. But i'll leave it,
-- because i have original function written with it..
data Remainder4 : Nat -> Nat -> Type where
  MkRem4 : {n, m : Nat} ->
          {auto lte : m `LTE` n} ->
          (k, r : Nat) -> {auto 0 prfN : n = k*m + r} -> {auto 0 prfR : r `LTE` m} ->
          Remainder4 n m

multOneRight : (n : Nat) -> n `mult` 1 = n

multDistOverPlusLeft : (a, b, c : Nat) -> (a + b) * c = a * c + b * c

multDistOverPlusRight : (a, b, c : Nat) -> a * (b + c) = a * b + a * c

multSuccLeft : (a, b : Nat) -> (a + 1) * b = b + a * b

-- This is original version of findRemainder3' with proofs using `rewrite`.
-- These proofs are almost unreadable, so just leave it as is..
total
findRemainder4 : (n : Nat) -> {auto u : Nat} -> {auto upper : n `LTE` u} ->
     (m : Nat) -> {auto lte : S m `LTE` n} -> Remainder4 n (S m)
findRemainder4 {upper = LTEZero} Z Z impossible
findRemainder4 n Z = MkRem4 n 0 {prfN = rewrite multOneRight n in
                           rewrite plusZeroRightNeutral n in
                                   Refl}
findRemainder4 n {u = S u'} m with (minusLte n (S m)) proof 0 minusPrf
  _ | Z = MkRem4 1 0 {prfN =  rewrite plusZeroRightNeutral m in
                             rewrite plusZeroRightNeutral m in
                                     minusEqZero n (S m) minusPrf}
  _ | (S t) with (decEq (S m) (S t))
    _ | Yes prf = MkRem4 2 0 {prfN = rewrite plusZeroRightNeutral m in
                                    rewrite plusZeroRightNeutral (plus m (S m)) in
                                    rewrite prf in
                                    minusEqPlus n (S m) (S t) minusPrf}
    _ | No contra with (connex contra {rel = LTE})
      _ | Left smLteSk =
              -- Either use the same proof as in f, or..
              let upPrf : S (m + (S t)) `LTE` S u'
                  upPrf = rewrite sym (minusEqPlus n (S m) (S t) minusPrf) in upper
                  rec = findRemainder4 (S t) {u = u'} m {upper = plusRightLte (ltePred upPrf)} {lte = smLteSk}
              in case rec of
                  MkRem4 k r {prfN = prfN} {prfR = prfR} =>
                    MkRem4 (k+1) r {prfR = prfR}
                                  {prfN = rewrite multDistOverPlusLeft k 1 (S m) in
                                          rewrite plusZeroRightNeutral m in
                                          rewrite minusEqPlus n (S m) (S t) minusPrf in
                                          rewrite prfN in
                                          rewrite sym (plusSuccRightSucc (mult k (S m)) m) in
                                          rewrite plusCommutative (mult k (S m)) m in
                                          rewrite sym (plusAssociative m (mult k (S m)) r) in
                                                  Refl}
      _ | Right skLteSm =
              MkRem4 1 (S t) {prfR = skLteSm}
                            {prfN = rewrite plusZeroRightNeutral m in
                                    minusEqPlus n (S m) (S t) minusPrf}

-- Finally, use of minusEqPlus almost in every branch above in findRemainder3
-- and findRemainder4 suggests, that i don't need `minus` at all! Maybe use
-- plus in the first place instead? Like this view:
data SumView1 : Nat -> Nat -> Type where
  MkSumView1 : {n, m : Nat} -> {auto lte : m `LTE` n} ->
              (q : Nat) -> {sumPrf : n = q + m} -> SumView1 n m
  NoSumView1 : {auto nLTm : n `LT` m} -> SumView1 n m

sumView1 : (n, m : Nat) -> SumView1 n m
sumView1 Z Z = MkSumView1 0 {sumPrf = Refl}
sumView1 Z (S m') = NoSumView1
sumView1 (S n') Z = MkSumView1 (S n') {sumPrf = rewrite plusZeroRightNeutral n' in Refl}
sumView1 (S n') (S m') =
  case sumView1 n' m' of
       MkSumView1 q {lte} {sumPrf} =>
         MkSumView1 q {sumPrf = rewrite sym (plusSuccRightSucc q m') in cong S sumPrf}
       NoSumView1 => NoSumView1

-- I don't need to embed proofs into datatype though. Proofs will be
-- automatically available in functions, which _can_ represent Nat-s as
-- SumView1.
data SumView : Nat -> Nat -> Type where
  MkSumView : (q : Nat) -> SumView (m + q) m
  NoSumView : {auto nLTm : n `LT` m} -> SumView n m

sumView2 : (n, m : Nat) -> SumView n m
sumView2 Z Z = MkSumView 0
sumView2 Z (S m') = NoSumView
sumView2 (S n') Z = MkSumView (S n')
sumView2 (S n') (S m') =
  case sumView2 n' m' of
       MkSumView q => MkSumView q
       NoSumView {nLTm} => NoSumView

-- And, finally, tail recursive version using SumView instead of `minus`.
findRemainder5' : (n : Nat) -> {auto upper : n `LTE` u} ->
                 (m : Nat) -> {auto 0 isS : IsSucc m} ->
                 (kAcc : Nat) -> Remainder1 (kAcc*m + n) m
findRemainder5' n (S m') kAcc {upper} with (sumView2 n (S m'))
  _ | NoSumView {nLTm} = MkRem1 kAcc n
  findRemainder5' (S (m' + q)) (S m') kAcc {upper = LTESucc up} | MkSumView q =
    let rec = findRemainder5' q (S m') (S kAcc) {upper = plusRightLte {n = m'} up}
        eqPrf : kAcc * S m' + S (m' + q) === (S kAcc) * (S m') + q
        eqPrf = Calc $
                  |~ kAcc * S m' + (S m' + q)
                  ~~ (kAcc * S m' + S m') + q
                        ...(plusAssociative (kAcc*S m') (S m') q)
                  ~~ (S m' + kAcc * S m') + q
                        ...(rewrite plusCommutative (kAcc*S m') (S m') in Refl)
                  ~~ (S kAcc * S m') + q ...(Refl)
    in rewrite eqPrf in rec

export
findRemainder5 : (n : Nat) -> (m : Nat) -> {auto 0 isS : IsSucc m} -> Remainder1 n m
findRemainder5 n m = findRemainder5' n {upper = lteSelf} m 0

-- And, finally, i don't need prfN proof in Remainder type as separate
-- argument as well: i may move it into type and function, which can build
-- MkRem will provide the proof automatically. Also as a consequence `n`
-- becomes unsolvable from the type: it does not mentioned in type now and
-- from just having `MkRem 1 0` i can't infer what `n` was. But now i don't
-- need `n` in type at all!
public export
data Remainder : Nat -> Nat -> Type where
  MkRem : {0 m : Nat} -> {auto 0 isS : IsSucc m} ->
          (k, r : Nat) -> {auto prfR : r `LT` m} ->
          Remainder (k*m + r) m

export
Eq (Remainder n m) where
  _ == _ = True

findRemainder' : (n : Nat) -> {auto upper : n `LTE` u} ->
                 (m : Nat) -> {auto 0 isS : IsSucc m} ->
                 (kAcc : Nat) -> Remainder (kAcc*m + n) m
findRemainder' n (S m') kAcc {upper} with (sumView2 n (S m'))
  _ | NoSumView {nLTm} = MkRem kAcc n
  findRemainder' (S (m' + q)) (S m') kAcc {upper = LTESucc up} | MkSumView q =
    let rec = findRemainder' q (S m') (S kAcc) {upper = plusRightLte {n = m'} up}
        eqPrf : kAcc * S m' + S (m' + q) === (S kAcc) * (S m') + q
        eqPrf = Calc $
                  |~ kAcc * S m' + (S m' + q)
                  ~~ (kAcc * S m' + S m') + q
                        ...(plusAssociative (kAcc*S m') (S m') q)
                  ~~ (S m' + kAcc * S m') + q
                        ...(rewrite plusCommutative (kAcc*S m') (S m') in Refl)
                  ~~ (S kAcc * S m') + q ...(Refl)
    in rewrite eqPrf in rec

export
findRemainder : (n : Nat) -> (m : Nat) -> {auto 0 isS : IsSucc m} -> Remainder n m
findRemainder n m = findRemainder' n {upper = lteSelf} m 0
