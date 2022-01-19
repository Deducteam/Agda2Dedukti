{-# OPTIONS --guardedness #-}
open import Agda.Builtin.Coinduction
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import nat-aux
open import eq-aux

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

data Stream (A : Set) : Set where
  [] : Stream A
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

zeros : Stream Nat
zeros = 0 ∷ ♯ zeros

natStream : Nat → Stream Nat
natStream n = n ∷ ♯ (natStream (suc n))

nth : {A : Set} → Nat → Stream A → Maybe A
nth zero (x ∷ l) = just x
nth (suc n) (x ∷ l) = nth n (♭ l)
nth _ [] = nothing

list-to-stream : {A : Set} → List A → Stream A
list-to-stream [] = []
list-to-stream (x ∷ l) = x ∷ ♯ (list-to-stream l)

stream-to-list : {A : Set} → Nat → Stream A → List A
stream-to-list zero _ = []
stream-to-list (suc n) [] = []
stream-to-list (suc n) (x ∷ l) = x ∷ (stream-to-list n (♭ l))

append : {A : Set} → List A → Stream A → Stream A
append [] s = s
append (x ∷ l) s = x ∷ ♯ (append l s)

data _~_ {A : Set} : Stream A → Stream A → Set where
  ~-empty : [] ~ []
  ~-cons  : {x x' : A} {l l' : ∞ (Stream A)} → x ≡ x' → ∞ (♭ l ~ ♭ l') → (x ∷ l) ~ (x' ∷ l')

~-refl : {A : Set} → (x : Stream A) → x ~ x
~-refl [] = ~-empty
~-refl (x ∷ l) = ~-cons refl (♯ (~-refl (♭ l)))

~-sym : {A : Set} → (x y : Stream A) → x ~ y → y ~ x
~-sym x y ~-empty = ~-empty
~-sym (x ∷ l) (x' ∷ l') (~-cons p q) = ~-cons (sym p) (♯ (~-sym _ _ (♭ q)))

~-trans : {A : Set} → (x y z : Stream A) → x ~ y → y ~ z → x ~ z
~-trans x y z ~-empty ~-empty = ~-empty
~-trans (x ∷ l) (x' ∷ l') (x'' ∷ l'') (~-cons p q) (~-cons p' q') = ~-cons (trans p p') (♯ (~-trans _ _ _ (♭ q) (♭ q')))


infix 21 _⊕_
_⊕_ : Stream Nat → Stream Nat → Stream Nat 
[]      ⊕ _         = []
(_ ∷ _) ⊕ []        = []
(x ∷ l) ⊕ (x' ∷ l') = (x + x') ∷ ♯ (♭ l ⊕ ♭ l')

⊕-trans : (l1 l2 l3 : Stream Nat) → (l1 ⊕ l2) ⊕ l3 ~ l1 ⊕ (l2 ⊕ l3)
⊕-trans [] _ _ = ~-empty
⊕-trans (_ ∷ _) [] _ = ~-empty
⊕-trans (_ ∷ _) (_ ∷ _) [] = ~-empty
⊕-trans (x1 ∷ l1) (x2 ∷ l2) (x3 ∷ l3) = ~-cons (+-assoc x1 x2 x3) (♯ (⊕-trans (♭ l1) (♭ l2) (♭ l3)))

⊕-com : (l k : Stream Nat) → l ⊕ k ~ k ⊕ l
⊕-com [] [] = ~-empty
⊕-com [] (_ ∷ _) = ~-empty
⊕-com (_ ∷ _) [] = ~-empty
⊕-com (x1 ∷ l1) (x2 ∷ l2) = ~-cons (+-com x1 x2) (♯ (⊕-com (♭ l1) (♭ l2)))

0-⊕ : (l : Stream Nat) → zeros ⊕ l ~ l
0-⊕ [] = ~-empty
0-⊕ (n ∷ l) = ~-cons refl (♯ (0-⊕ (♭ l)))
