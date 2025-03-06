
data Duration : Type where
  MkInt : (duration : Int) -> (tot : Double) -> Duration
  MkFloat : (duration : Double) -> (tot : Double) -> Duration

F : Duration -> Type
F (MkInt _ _) = Int
F (MkFloat _ _) = Double

adjust : (a : Duration) -> F a -> Duration
adjust (MkInt d tot) k = MkInt (d * (1 + k)) (tot * cast (1 + k))
adjust (MkFloat d tot) k = MkFloat (d * (1 + k)) (tot * (1 + k))

calcDuration : List Duration -> List Duration
