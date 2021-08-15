open import Agda.Builtin.Equality
open import Agda.Primitive

sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans p refl = p

cong : {A B : Set} -> {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

J : {l l' : Level} → (A : Set l) → (P : (a b : A) → a ≡ b → Set l') → ((a : A) → P a a refl) → (a b : A) → (p : a ≡ b) → P a b p
J = λ { A P x a .a refl → x a}

leib : (A : Set) → (a b : A) → a ≡ b → (P : A → Set) → P a → P b
leib = λ A → J A (λ a b p → (P : A → Set) → P a → P b) (λ a P x → x)


