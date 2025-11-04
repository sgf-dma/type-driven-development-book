
import Data.Nat

f2 : {n, d, q : Nat} -> n = plus (plus d (S n)) q -> n = (plus (S (plus n d)) q)
f2 h =
  let t = plusCommutative (S n) d
      t2 = replace {p = \y => n = plus y q} (sym t) h
  in  t2
  --in  rewrite t in h

f3 : {n, d, q : Nat} -> n = plus (plus d (S n)) q -> n = (plus (S (plus n d)) q)
f3 h =
  let t = plusCommutative (S n) d
      t2 = replace {p = \y => n = plus y q} (sym t) h
  in  rewrite plusSuccRightSucc (plus n d) q in
      rewrite plusCommutative n d in
      rewrite sym (plusAssociative d n (S q)) in
      rewrite plusAssociative n 1 q in
      rewrite plusAssociative d (plus n 1) q in
      rewrite plusCommutative n 1 in
      --rewrite plusAssociative (plus d n) 1 q in
      --rewrite sym (plusSuccRightSucc (plus d n) Z) in
      h

f4 : {n, d, q : Nat} -> n = plus (plus d (S n)) q -> n = (plus (S (plus n d)) q)
f4 h = do
    rewrite plusCommutative n d
    let prf : S (plus (plus d n) q) === plus (plus d (S n)) q
              = cong (`plus` q) $ plusSuccRightSucc d n
    rewrite prf
    h
