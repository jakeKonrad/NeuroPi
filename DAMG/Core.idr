module DAMG.Core

import Data.Nat

%prefix_record_projections off

public export
data G : (0 a : Nat -> Nat -> Type) -> Nat -> Nat -> Type where
  Vert : (m, n : Nat) -> a m n -> G a m n
  Edge : G a 1 1
  Beside : (m, n, p, q : Nat) -> G a m n -> G a p q -> G a (m + p) (n + q)
  Before : (m, n, p : Nat) -> G a m n -> G a n p -> G a m p
  Empty : G a 0 0
  Swap : (m, n : Nat) -> G a (m + n) (n + m)

public export
DBefore : (m, n, p, q : Nat) -> (0 prf : n = p) -> G a m n -> G a p q -> G a m q
DBefore m n p q prf x y = Before m n q x (rewrite prf in y) 

public export
Edges : (m : Nat) -> G a m m
Edges 0     = Empty
Edges (S k) = Beside 1 1 k k Edge (Edges k)

public export
record Cata (0 a : Nat -> Nat -> Type) (0 b : Nat -> Nat -> Type) where
  constructor MkCata
  empty : b 0 0
  edge : b 1 1
  vert : (m, n : Nat) -> a m n -> b m n
  swap : (m, n : Nat) -> b (m + n) (n + m)
  beside : (m, n, p, q : Nat) -> b m n -> b p q -> b (m + p) (n + q)
  before : (m, n, p : Nat) -> b m n -> b n p -> b m p

public export
cata : (0 m : Nat) -> (0 n : Nat) -> Cata a b -> G a m n -> b m n
cata m       n       h (Vert m n x)         = h.vert m n x 
cata 1       1       h Edge                 = h.edge
cata (m + p) (n + q) h (Beside m n p q x y) = h.beside m n p q (cata m n h x) (cata p q h y)
cata m       p       h (Before m n p x y)   = h.before m n p (cata m n h x) (cata n p h y)
cata 0       0       h Empty                = h.empty
cata (m + n) (n + m) h (Swap m n)           = h.swap m n

-- slight abuse of notation "dependent equality"
public export
DEqual : (0 b : Nat -> Nat -> Type) -> (0 prf : m = p) -> (0 prf1 : n = q) -> b m n -> b p q -> Type
DEqual b Refl Refl x y = x = y

public export
record IsLawful (0 a : Nat -> Nat -> Type) (0 b : Nat -> Nat -> Type) where
  constructor MkIsLawful
  h : Cata a b
  besideEmptyLeftNeutral : (m, n : Nat) 
                        -> (x : G a m n) 
                        -> Equal (cata m n h (Beside 0 0 m n Empty x))
                                 (cata m n h x) 
  besideEmptyRightNeutral : (m, n : Nat) 
                         -> (x : G a m n) 
                         -> DEqual b 
                                   (plusZeroRightNeutral m) 
                                   (plusZeroRightNeutral n) 
                                   (cata (m + 0) (n + 0) h (Beside m n 0 0 x Empty)) 
                                   (cata m n h x)
  besideAssociative : (m, n, p, q, r, s : Nat) 
                   -> (x : G a m n) 
                   -> (y : G a p q) 
                   -> (z : G a r s)
                   -> DEqual b 
                             (plusAssociative m p r) 
                             (plusAssociative n q s)
                             (cata (m + (p + r)) (n + (q + s)) h (Beside m n (p + r) (q + s) x (Beside p q r s y z)))
                             (cata ((m + p) + r) ((n + q) + s) h (Beside (m + p) (n + q) r s (Beside m n p q x y) z))
  beforeEdgesLeftNeutral : (m, n : Nat) 
                        -> (x : G a m n) 
                        -> Equal (cata m n h (Before m m n (Edges m) x)) 
                                 (cata m n h x)
  beforeEdgeRightNeutral : (m, n : Nat) 
                        -> (x : G a m n)
                        -> Equal (cata m n h (Before m n n x (Edges n)))
                                 (cata m n h x)
  beforeAssociative : (m, n, p, q : Nat) 
                   -> (x : G a m n) 
                   -> (y : G a n p)
                   -> (z : G a p q)
                   -> Equal (cata m q h (Before m n q x (Before n p q y z)))
                            (cata m q h (Before m p q (Before m n p x y) z))
  abiding : (m, n, p, q, r, s : Nat)
         -> (w : G a m n)
         -> (x : G a n p)
         -> (y : G a q r)
         -> (z : G a r s)
         -> Equal (cata (m + q) (p + s) h (Beside m p q s (Before m n p w x) (Before q r s y z)))
                  (cata (m + q) (p + s) h (Before (m + q) (n + r) (p + s) (Beside m n q r w y) (Beside n p r s x z)))
  swapZeroRightNeutral : (m : Nat) 
                      -> DEqual b
                                (plusZeroRightNeutral m)
                                Refl
                                (cata (m + 0) m h (Swap m 0))
                                (cata m m h (Edges m))
  swapPlus : (m, n, p : Nat)
          -> DEqual b
                    (plusAssociative m n p)
                    (sym (plusAssociative n p m)) 
                    (cata (m + (n + p)) ((n + p) + m) h (Swap m (n + p)))
                    (cata ((m + n) + p) 
                          (n + (p + m)) 
                          h 
                          (DBefore ((m + n) + p)
                                   ((n + m) + p)
                                   (n + (m + p))
                                   (n + (p + m))
                                   (sym (plusAssociative n m p))
                                   (Beside (m + n) (n + m) p p (Swap m n) (Edges p)) 
                                   (Beside n n (m + p) (p + m) (Edges n) (Swap m p))))
  swapLaw : (m, n, p, q : Nat)
         -> (x : G a n p)
         -> (y : G a m q)
         -> Equal (cata (m + n) 
                        (q + p) 
                        h 
                        (Before (m + n) 
                                (n + m) 
                                (q + p) 
                                (Swap m n) 
                                (Before (n + m) (p + q) (q + p) (Beside n p m q x y) (Swap p q))))
                  (cata (m + n) (q + p) h (Beside m q n p y x))
