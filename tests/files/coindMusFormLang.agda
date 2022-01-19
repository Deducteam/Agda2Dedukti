{-# OPTIONS --guardedness #-}
open import Agda.Builtin.Coinduction
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Equality

not : Bool → Bool
not true  = false
not false = true

_∨_ : Bool → Bool → Bool
true  ∨ x = true
false ∨ x = x

sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans p refl = p

∨-assoc : (a b c : Bool) → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
∨-assoc true  _ _ = refl
∨-assoc false _ _ = refl

∨-comm : (a b : Bool) → a ∨ b ≡ b ∨ a
∨-comm true  true  = refl
∨-comm true  false = refl
∨-comm false true  = refl
∨-comm false false = refl

∨-idem : (a : Bool) → a ∨ a ≡ a
∨-idem true  = refl
∨-idem false = refl


data Lang (A : Set) : Set where
  cons : Bool → (A → ∞ (Lang A)) → Lang A

_∈_ : {A : Set} → List A → Lang A → Bool
[] ∈ (cons ν δ) = ν
(a ∷ ls) ∈ (cons v δ) = ls ∈ (♭ (δ a))

trie : {A : Set} → (f : List A → Bool) → Lang A
trie f = cons (f []) (λ a → ♯ (trie (λ ls → f (a ∷ ls))))

∅ : {A : Set} → Lang A
∅ = cons false (λ _ → ♯ ∅)

ε : {A : Set} → Lang A
ε = cons true (λ _ → ♯ ∅)
