open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool


trans : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans p refl = p

cong : {A B : Set} -> {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

+-assoc : (x y z : Nat) -> (x + y) + z ≡ x + (y + z)
+-assoc 0 y z = refl
+-assoc (suc x) y z = cong suc (+-assoc x y z)
