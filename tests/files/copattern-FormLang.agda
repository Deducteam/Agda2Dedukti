{-# OPTIONS --guardedness  #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import bool-aux
open import eq-aux


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

A* : {A : Set} → Lang A
ν A* = true
δ A* _ = A*

ε : {A : Set} → Lang A
ν ε   = true
δ ε _ = ∅

¬ : {A : Set} → Lang A → Lang A
ν (¬ l)   = not (ν l)
δ (¬ l) x = ¬ (δ l x)

_∪_ : {A : Set} → Lang A → Lang A → Lang A
ν (l ∪ s)   =  ν l ∨ ν s
δ (l ∪ s) x =  δ l x ∪ δ s x

_∩_ : {A : Set} → Lang A → Lang A → Lang A
ν (l ∩ s)   =  ν l ∧ ν s
δ (l ∩ s) x =  δ l x ∩ δ s x

infix 21 _·_

{-# TERMINATING #-}
_·_ : ∀ {A} → Lang A → Lang A → Lang A
ν (a · b)   = ν a ∧ ν b
δ (a · b) x = if ν a then δ a x · b ∪ δ b x else δ a x · b

{-# TERMINATING #-}
_* : ∀ {A} → Lang A → Lang A
ν (a *)   = true
δ (a *) x = δ a x · (a *)


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

∪-cong : {A : Set} → {l' s' : Lang A} → (l s : Lang A) → l ≈ l' → s ≈ s' → l ∪ s ≈ l' ∪ s'
≈ν (∪-cong l s p q) = ∨-cong (ν l) (ν s) (≈ν p) (≈ν q)
≈δ (∪-cong l s p q) x = ∪-cong (δ l x) (δ s x) (≈δ p x) (≈δ q x)

∩-assoc : {A : Set} → (l s k : Lang A) → (l ∩ s) ∩ k ≈ l ∩ (s ∩ k)
≈ν (∩-assoc l s k)   = ∧-assoc (ν l) (ν s) (ν k)
≈δ (∩-assoc l s k) a = ∩-assoc (δ l a) (δ s a) (δ k a)

∩-comm : {A : Set} → (l s : Lang A) → l ∩ s ≈ s ∩ l
≈ν (∩-comm l s)   = ∧-comm (ν l) (ν s)
≈δ (∩-comm l s) a = ∩-comm (δ l a) (δ s a)

∩-idem : {A : Set} → (l : Lang A) → l ∩ l ≈ l
≈ν (∩-idem l)   = ∧-idem (ν l)
≈δ (∩-idem l) a = ∩-idem (δ l a)

∩-cong : {A : Set} → {l' s' : Lang A} → (l s : Lang A) → l ≈ l' → s ≈ s' → l ∩ s ≈ l' ∩ s'
≈ν (∩-cong l s p q) = ∧-cong (ν l) (ν s) (≈ν p) (≈ν q)
≈δ (∩-cong l s p q) x = ∩-cong (δ l x) (δ s x) (≈δ p x) (≈δ q x)

∪-unit₁ : {A : Set} → (l : Lang A) → ∅ ∪ l ≈ l
≈ν (∪-unit₁ l)   = refl
≈δ (∪-unit₁ l) a = ∪-unit₁ (δ l a)

∪-unit₂ : {A : Set} → (l : Lang A) → l ∪ ∅ ≈ l
∪-unit₂ l = ≈trans (∪-comm l ∅) (∪-unit₁ l)

∩-unit₁ : {A : Set} → (l : Lang A) → A* ∩ l ≈ l
≈ν (∩-unit₁ l)   = refl
≈δ (∩-unit₁ l) a = ∩-unit₁ (δ l a)

∩-unit₂ : {A : Set} → (l : Lang A) → l ∩ A* ≈ l
∩-unit₂ l = ≈trans (∩-comm l A*) (∩-unit₁ l)

∪-∩-dist : {A : Set} → (l s k : Lang A) → l ∪ (s ∩ k) ≈ (l ∪ s) ∩ (l ∪ k)
≈ν (∪-∩-dist l s k) = ∨-∧-dist (ν l) (ν s) (ν k)
≈δ (∪-∩-dist l s k) x = ∪-∩-dist (δ l x) (δ s x) (δ k x)

∩-∪-dist : {A : Set} → (l s k : Lang A) → l ∩ (s ∪ k) ≈ (l ∩ s) ∪ (l ∩ k)
≈ν (∩-∪-dist l s k) = ∧-∨-dist (ν l) (ν s) (ν k)
≈δ (∩-∪-dist l s k) x = ∩-∪-dist (δ l x) (δ s x) (δ k x)

∪-comp : {A : Set} → (l : Lang A) → l ∪ (¬ l) ≈ A*
≈ν (∪-comp l) = ∨-comp (ν l)
≈δ (∪-comp l) x = ∪-comp (δ l x)

∩-comp : {A : Set} → (l : Lang A) → l ∩ (¬ l) ≈ ∅
≈ν (∩-comp l) = ∧-comp (ν l)
≈δ (∩-comp l) x = ∩-comp (δ l x)

-- 31 until here

-- deterministic automata
record DA (S : Set) (A : Set): Set where
  field
    ν : (s : S) → Bool
    δ : (s : S) (a : A) → S
open DA    

lang : ∀{A S} (da : DA S A) (s : S) → Lang A
Lang.ν (lang da s) = ν da s
Lang.δ (lang da s) a = lang da (δ da s a)

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_    
  
_⊕_ : ∀{S S' A} (da : DA S A) (da' : DA S' A) → DA (S × S') A
ν (da ⊕ da') (s , s' ) = ν da s ∨ ν da' s'
δ (da ⊕ da') (s , s' ) a = δ da s a , δ da' s' a

⊕-is-∪ : ∀{S S' A} (da : DA S A) (da' : DA S' A) → (s : S) → (s' : S') → lang (da ⊕ da') (s , s' ) ≈ (lang da s) ∪ (lang da' s')
≈ν (⊕-is-∪ da da' s s') = refl
≈δ (⊕-is-∪ da da' s s') x = ⊕-is-∪ da da' (δ da s x) (δ da' s' x)

_⊗_ : ∀{S S' A} (da : DA S A) (da' : DA S' A) → DA (S × S') A
ν (da ⊗ da') (s , s' ) = ν da s ∧ ν da' s'
δ (da ⊗ da') (s , s' ) a = δ da s a , δ da' s' a

⊗-is-∩ : ∀{S S' A} (da : DA S A) (da' : DA S' A) → (s : S) → (s' : S') → lang (da ⊗ da') (s , s' ) ≈ (lang da s) ∩ (lang da' s')
≈ν (⊗-is-∩ da da' s s') = refl
≈δ (⊗-is-∩ da da' s s') x = ⊗-is-∩ da da' (δ da s x) (δ da' s' x)

inv : {S A : Set} → DA S A → DA S A
ν (inv da) s = not (ν da s)
δ (inv da) s a = δ da s a

inv-is-¬ : ∀{S A} (da : DA S A) (s : S) → lang (inv da) s ≈ ¬ (lang da s)
≈ν (inv-is-¬ da s) = refl
≈δ (inv-is-¬ da s) x = inv-is-¬ da (δ da s x)

∅A : ∀{A} → DA ⊤ A
ν ∅A s = false
δ ∅A s a = s

∅A-is-∅ : {A : Set} → (s : ⊤) → lang (∅A {A}) s ≈ ∅
≈ν (∅A-is-∅ _) = refl
≈δ (∅A-is-∅ s) _ = ∅A-is-∅ s

εA : ∀{A} → DA Bool A
ν εA s = s
δ εA s a = false

εA-is-ε' : {A : Set} → lang (εA {A}) false ≈ ∅
≈ν εA-is-ε' = refl
≈δ εA-is-ε' _ = εA-is-ε'

εA-is-ε : {A : Set} → lang (εA {A}) true ≈ ε
≈ν εA-is-ε = refl
≈δ εA-is-ε _ = εA-is-ε'



-- 37 until here
