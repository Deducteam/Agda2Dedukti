open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

record R : Set where
  constructor cons
  field n : Nat

bla : ∀ (x : R) -> x ≡ cons (R.n x)
bla x = refl

bla2 : ∀ {A : Set} (x : A → A) -> x ≡ λ y -> x y
bla2 x = refl
