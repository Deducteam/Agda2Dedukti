open import Agda.Builtin.Nat

record Pair (A : Set) : Set where
  field
    n1 : Nat → A
    n2 : A

open Pair

el : Nat -> Nat -> Pair Nat
n1 (el x y) n = x + n
n2 (el x y) = y
