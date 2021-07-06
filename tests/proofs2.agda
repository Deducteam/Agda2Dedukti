open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a
infix 4 _≡_


trans : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans p refl = p

cong : {A B : Set} -> {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

+-assoc : (x y z : Nat) -> (x + y) + z ≡ x + (y + z)
+-assoc 0 y z = refl
+-assoc (suc x) y z = cong suc (+-assoc x y z)
