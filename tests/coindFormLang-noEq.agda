{-# OPTIONS --guardedness  #-}
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

data List (A : Set) : Set where
  _∷_ : A → List A → List A
  [] : List A
infixr 5 _∷_  

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a
infix 4 _≡_

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

record Lang (A : Set) : Set where
  coinductive
  field ν : Bool
  field δ : A → Lang A
open Lang

_∈_ : {A : Set} → List A → Lang A → Bool
[] ∈ l       = ν l
(a ∷ ls) ∈ l = ls ∈ (δ l a) 

trie : {A : Set} → (f : List A → Bool) → Lang A
ν (trie f)   = f []
δ (trie f) a = trie (λ ls → f (a ∷ ls))

∅ : {A : Set} → Lang A
ν ∅   = false
δ ∅ _ = ∅

ε : {A : Set} → Lang A
ν ε   = true
δ ε _ = ∅

¬ : {A : Set} → Lang A → Lang A
ν (¬ l)   = not (ν l)
δ (¬ l) x = ¬ (δ l x)

_∪_ : {A : Set} → Lang A → Lang A → Lang A
ν (l ∪ s)   =  (ν l) ∨ (ν s)
δ (l ∪ s) x =  (δ l x) ∪ (δ s x)

infix 4 _≈_
record _≈_ {A : Set} (l : Lang A) (s : Lang A) : Set where
  coinductive
  field ≈ν : ν l ≡ ν s
  field ≈δ : (a : A) → δ l a ≈ δ s a
open _≈_

≈refl : {A : Set} → {l : Lang A} → l ≈ l
≈ν ≈refl   = refl
≈δ ≈refl _ = ≈refl

≈sym : {A : Set} → {l s : Lang A} → l ≈ s → s ≈ l
≈ν (≈sym p)    = sym (≈ν p)
≈δ (≈sym p) a  = ≈sym (≈δ p a)

≈trans : {A : Set} → {l s k : Lang A} → l ≈ s → s ≈ k → l ≈ k
≈ν (≈trans p q)   = trans (≈ν p) (≈ν q)
≈δ (≈trans p q) a = ≈trans (≈δ p a) (≈δ q a)

∪-assoc : {A : Set} → (l s k : Lang A) → (l ∪ s) ∪ k ≈ l ∪ (s ∪ k)
≈ν (∪-assoc l s k)   = ∨-assoc (ν l) (ν s) (ν k)
≈δ (∪-assoc l s k) a = ∪-assoc (δ l a) (δ s a) (δ k a)

∪-comm : {A : Set} → (l s : Lang A) → l ∪ s ≈ s ∪ l
≈ν (∪-comm l s)   = ∨-comm (ν l) (ν s)
≈δ (∪-comm l s) a = ∪-comm (δ l a) (δ s a)

∪-idem : {A : Set} → (l : Lang A) → l ∪ l ≈ l
≈ν (∪-idem l)   = ∨-idem (ν l)
≈δ (∪-idem l) a = ∪-idem (δ l a)

∪-unit₁ : {A : Set} → (l : Lang A) → ∅ ∪ l ≈ l
≈ν (∪-unit₁ l)   = refl
≈δ (∪-unit₁ l) a = ∪-unit₁ (δ l a)

∪-unit₂ : {A : Set} → (l : Lang A) → l ∪ ∅ ≈ l
∪-unit₂ l = ≈trans (∪-comm l ∅) (∪-unit₁ l)

