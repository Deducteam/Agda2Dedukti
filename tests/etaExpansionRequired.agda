
open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

variable
  a : Level
  A : Set a

record R {a : Level} (A : Set a) : Set (lsuc a) where
  constructor cons
  field n : Nat
  field m : A

f : R A -> Nat -> R Nat
f (cons n m) x = cons x n

bla : ∀ (x : R Nat) -> x ≡ cons (R.n x) (R.m x)
bla x = refl

bla2 : ∀ (x : A → A) -> x ≡ λ y -> x y
bla2 x = refl
