{-# OPTIONS --guardedness #-}
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import eq-aux
open import nat-aux

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A
open Stream

nth : {A : Set} -> Nat -> Stream A -> A
nth 0 x = hd x
nth (suc n) x = nth n (tl x)

zeros : Stream Nat
hd zeros = 0
tl zeros = zeros

natStream : (n : Nat) → Stream Nat
hd (natStream n) = n
tl (natStream n) = natStream (suc n)

-- after the list is over, continues with 'end'
list-to-stream : {A : Set} → (end : A) → List A → Stream A
hd (list-to-stream end []) = end 
tl (list-to-stream end []) = list-to-stream end []
hd (list-to-stream end (x ∷ l)) = x
tl (list-to-stream end (x ∷ l)) = list-to-stream end l

stream-to-list : {A : Set} → Nat → Stream A → List A
stream-to-list zero _ = []
stream-to-list (suc n) s = (hd s) ∷ (stream-to-list n (tl s))

append : {A : Set} → List A → Stream A → Stream A
append [] s = s
hd (append (x ∷ l) s) = x
tl (append (x ∷ l) s) = append l s

stream-fare-comp' : {A : Set} → Stream (Stream A) → List (Stream A) → List (Stream A) → Stream A
hd (stream-fare-comp' s [] l) = hd (hd s)
tl (stream-fare-comp' s [] l) = stream-fare-comp' (tl s) l (tl (hd s) ∷ [])
hd (stream-fare-comp' s (x ∷ l) l') = hd x
tl (stream-fare-comp' s (x ∷ l) l') = stream-fare-comp' s l ((tl x) ∷ l')

-- fare composition of streams, goes through the diagonal, like when enumerating the rationals
stream-fare-comp : {A : Set} → Stream (Stream A) → Stream A
stream-fare-comp s = stream-fare-comp' s [] []

-- to test stream-fare-comp we can do stream-to-list 20 (stream-fare-comp (natStreamStream 0))
natStreamStream : Nat → Stream (Stream Nat)
hd (natStreamStream n) = natStream n
tl (natStreamStream n) = natStreamStream (suc n)

record _≈_ {A} (xs : Stream A) (ys : Stream A) : Set where
  coinductive
  field
    hd-≡ : hd xs ≡ hd ys
    tl-≈ : tl xs ≈ tl ys
open _≈_

refl-≈ : {A : Set} -> {s : Stream A} -> s ≈ s
hd-≡ (refl-≈ {_} {s}) = refl
tl-≈ (refl-≈ {_} {s}) = refl-≈ {_} {tl s}

sym-≈ : {A : Set} -> {s s' : Stream A} -> s ≈ s' → s' ≈ s
hd-≡ (sym-≈ p) = sym (hd-≡ p)
tl-≈ (sym-≈ p) = sym-≈ (tl-≈ p)

trans-≈ : {A : Set} -> {x y z : Stream A} -> x ≈ y -> y ≈ z -> x ≈ z
hd-≡ (trans-≈ p q) = trans (hd-≡ p) (hd-≡ q)
tl-≈ (trans-≈ p q) = trans-≈ (tl-≈ p) (tl-≈ q)

≡to≈ : {A : Set} -> {x y : Stream A} -> x ≡ y -> x ≈ y
≡to≈ refl = refl-≈

cong-≈ : {A B : Set} -> {x y : A} -> (f : A -> Stream B) -> x ≡ y -> f x ≈ f y
hd-≡ (cong-≈ f p) = cong (λ x -> hd (f x)) p
tl-≈ (cong-≈ f p) = cong-≈ tl (cong f p)

_⊕_ : Stream Nat → Stream Nat → Stream Nat
hd (x ⊕ y) = (hd x) + (hd y)
tl (x ⊕ y) = (tl x) ⊕ (tl y)

infix 21 _⊕_
⊕-assoc : (x y z : Stream Nat) → (x ⊕ y) ⊕ z ≈ x ⊕ (y ⊕ z)
hd-≡ (⊕-assoc x y z) = +-assoc (hd x) (hd y) (hd z)
tl-≈ (⊕-assoc x y z) = ⊕-assoc (tl x) (tl y) (tl z)

⊕-com : (x y : Stream Nat) → x ⊕ y ≈ y ⊕ x
hd-≡ (⊕-com x y) = +-com (hd x) (hd y)
tl-≈ (⊕-com x y) = ⊕-com (tl x) (tl y)

⊕-zeros : (x : Stream Nat) → zeros ⊕ x ≈ x
hd-≡ (⊕-zeros x) = refl
tl-≈ (⊕-zeros x) = ⊕-zeros (tl x)

-- miscellaneous properties of streams

tailn : {A : Set} -> (n : Nat) -> Stream A -> Stream A
tailn 0 x = x
tailn (suc n) x = tl (tailn n x)

tailNatS : (n : Nat) -> tailn n (natStream 0) ≈ natStream n
tailNatS 0 = refl-≈
tailNatS (suc n) = tl-≈ (tailNatS n)

plusS : (n : Nat) -> Stream Nat -> Stream Nat
hd (plusS n x) = n + (hd x)
tl (plusS n x) = plusS n (tl x)

etaPlusS : (x : Stream Nat) -> x ≈ plusS 0 x
hd-≡ (etaPlusS x) = refl
tl-≈ (etaPlusS x) = etaPlusS (tl x)

plusS+ : (n m : Nat) -> (x : Stream Nat) -> plusS (n + m) x ≈ plusS n (plusS m x)
hd-≡ (plusS+ n m x) = +-assoc n m (hd x)
tl-≈ (plusS+ n m x) = plusS+ n m (tl x)

posNatS2 : (n m : Nat) -> nth n (tl (natStream m)) ≡ suc (nth n (natStream m))
posNatS2 0 m = refl
posNatS2 (suc n) m = posNatS2 n (suc m)

posNatS : (m n : Nat) -> nth (suc n) (natStream m) ≡ nth n (natStream (suc m))
posNatS n m = refl

posNatS+ : (n m : Nat) -> nth n (natStream m) ≡ n + m
posNatS+ 0 m = refl
posNatS+ (suc n) m  = trans (posNatS2 n m) (cong suc (posNatS+ n m))

