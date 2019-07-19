
open import Agda.Primitive
open import Agda.Builtin.Nat

record r : Set where
  constructor cons
  field n : Nat
  field m : Nat

record rr (A : Set) : Set where
  constructor conss
  field nn : A
