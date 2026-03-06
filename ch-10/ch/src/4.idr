-- rejected by termination checker
total
foo : Nat -> ()
foo (S (S k)) 
 _ | _ = foo (S k)
foo _ = ()

-- accepted
total
bar : Nat -> ()
bar (S m@(S k)) with ()
 _ | _ = bar m
bar _ = ()
