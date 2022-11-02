module NeuroPi.SubModule

public export
data SubModule : (0 a : Nat -> Type) -> Nat -> Nat -> Type where
  Node     : (n : Nat) -> a n -> SubModule a n 1
  Beside   : (n, p, q : Nat) -> SubModule a n p -> SubModule a n q -> SubModule a n (p + q)
  Before   : (n, p, q : Nat) -> SubModule a n p -> SubModule a (n + p) q -> SubModule a n (p + q)
  Feedback : (n, p : Nat) -> SubModule a (n + p) p -> SubModule a n p

%name SubModule f, g

