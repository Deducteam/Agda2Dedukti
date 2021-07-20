{-# OPTIONS --guardedness #-}
open import Agda.Builtin.Coinduction
open import Agda.Builtin.Nat

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A


makeStream : Nat → Stream Nat
makeStream n = n ∷ ♯ (makeStream n)

times2 : Stream Nat → Stream Nat
times2 (hd ∷ tl) = (hd + hd) ∷ ♯ (times2 (♭ tl))

nth : Nat → Stream Nat → Nat
nth zero (hd ∷ tl) = hd
nth (suc n) (hd ∷ tl) = nth n (♭ tl)

zeros = 0 ∷ (♯ zeros)


-- A stream processor SP A B consumes elements of A and produces
-- elements of B. It can only consume a finite number of A’s before
-- producing a B.

data SP (A B : Set) : Set where
  get : (f : A → SP A B) → SP A B
  put : (b : B) (sp : ∞ (SP A B)) → SP A B

-- The function eat is defined by an outer corecursion into Stream B
-- and an inner recursion on SP A B.

eat : ∀ {A B} → SP A B → Stream A → Stream B
eat (get f)    (a ∷ as) = eat (f a) (♭ as)
eat (put b sp) as       = b ∷ ♯ eat (♭ sp) as

-- Composition of stream processors.

_∘_ : ∀ {A B C} → SP B C → SP A B → SP A C
get f₁    ∘ put x sp₂ = f₁ x ∘ ♭ sp₂
put x sp₁ ∘ sp₂       = put x (♯ (♭ sp₁ ∘ sp₂))
sp₁       ∘ get f₂    = get (λ x → sp₁ ∘ f₂ x)
