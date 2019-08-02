
open import Agda.Primitive
open import Agda.Builtin.Nat

variable
  a : Level
  A : Set a

record R {a : Level} (A : Set a) : Set (lsuc a) where
  constructor cons
  field n : Nat
  field m : A


f : R A -> Nat -> R Nat
f (cons n m) x = cons x n

g : Nat -> R A -> R Nat
g x (cons n m) = cons x n
