module NeuroPi.Module

import NeuroPi.SubModule

public export
data Module : (0 a : Nat -> Type) -> Nat -> Nat -> Type where
  MkModule : (input, hidden, output : Nat) 
          -> SubModule a input hidden 
          -> SubModule a (input + hidden) output
          -> Module a input output

