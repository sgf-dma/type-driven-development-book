
import Data.List
import Data.Nat

divHalf : (n : Nat) -> Nat
divHalf Z = Z
divHalf (S Z) = Z
divHalf (S (S t)) = S (divHalf t)

total
divHalfSuccLteSelf : (n : Nat) -> divHalf (S n) `LTE` n
divHalfSuccLteSelf Z = LTEZero
divHalfSuccLteSelf (S Z) = LTESucc LTEZero
divHalfSuccLteSelf (S (S k)) = let rec = divHalfSuccLteSelf k in LTESucc (lteSuccRight rec)

total
splitConsSndLteSucc : (y : a) -> {n, m : Nat} -> {xs : List a} ->
                        length (snd (splitAt n     xs))  `LTE` m ->
                        length (snd (splitAt n (y::xs))) `LTE` S m
splitConsSndLteSucc _ {n = Z} {xs = xs} lte = LTESucc lte
splitConsSndLteSucc _ {n = (S Z)} {xs = []} _ = LTEZero
splitConsSndLteSucc _ {n = (S (S k))} {xs = []} _ = LTEZero
splitConsSndLteSucc y {n = (S k)} {xs = x::xs'} lte with (splitAt k xs') proof 0 eq
  _ | (l, r) with (splitAt k (x::xs')) proof 0 eq2
    _ | (xl, xr) =
        let rec = splitConsSndLteSucc x {n = k} {m = m} {xs = xs'} (rewrite eq in lte)
        in rewrite cong snd (sym eq2) in rec

total
splitHalfSndLteHalfSucc : (xs : List a) ->
                    length (snd (splitAt (divHalf (length xs)) xs)) `LTE` (divHalf (S (length xs)))
splitHalfSndLteHalfSucc [] = ?b1
splitHalfSndLteHalfSucc (x::xs') = ?b2
splitHalfSndLteHalfSucc (x1::x2::xs') with (splitAt (divHalf (length xs')) (x2::xs')) proof 0 eq
  _ | (l, r) =
      let rec = splitConsSndLteSucc x2 (splitHalfSndLteHalfSucc xs')
      in  rewrite cong snd (sym eq) in rec

total
f5 : (xs : List Int) -> {m : Nat} -> {auto prf : length xs `LTE` m} -> Int
f5 [] = 0
f5 [x] = x
f5 (_::x2::xs') {m = S Z} {prf = LTESucc lte} = absurd lte
f5 (_::x2::xs') {m = S (S k)} {prf = LTESucc lte} with (splitAt (divHalf (length xs')) (x2::xs')) proof 0 eq
  _ | (l, r) =
      let
          sndPrf : LTE (length r) (S (divHalf (S (length xs'))))
                  = rewrite cong snd (sym eq) in
                            splitConsSndLteSucc x2 (splitHalfSndLteHalfSucc xs')
          prf3 : LTE (S (divHalf (S (length xs')))) (S (length xs'))
                  = LTESucc (divHalfSuccLteSelf (length xs'))
          recPrf : LTE (length r) (S k)
                  = (sndPrf `transitive` prf3) `transitive` lte
          rec = f5 r {m = S k} {prf = recPrf}
      in ?c3

