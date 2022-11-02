module DAMG.NN

import Data.Vect
import DAMG.Core

nnCata : Cata (\m, n => Vect m Double) (\m, n => Vect m Double -> Vect n Double)
nnCata = MkCata (\xs => xs) (\xs => xs) nnVert nnSwap nnBeside (\m, n, p, f, g => g . f)
  where
    nnVert : (m, n : Nat) -> Vect m Double -> Vect m Double -> Vect n Double 
    nnVert m n ws xs = replicate n (sum (zipWith (*) ws xs))
    nnSwap : (m, n : Nat) -> Vect (m + n) Double -> Vect (n + m) Double
    nnSwap m n xs = let (ys, zs) = splitAt m xs in (zs ++ ys) 
    nnBeside : (m, n, p, q : Nat) 
            -> (Vect m Double -> Vect n Double) 
            -> (Vect p Double -> Vect q Double) 
            -> Vect (m + p) Double 
            -> Vect (n + q) Double
    nnBeside m n p q f g xs = let (ys, zs) = splitAt m xs in f ys ++ g zs

export
NN : Nat -> Nat -> Type
NN = G (\m, n => Vect m Double)

export
eval : NN m n -> Vect m Double -> Vect n Double
eval {m} {n} = cata m n nnCata

