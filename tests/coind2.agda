{-# OPTIONS --guardedness #-}
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import proofs2

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A

open Stream

zeros : Stream Nat
hd zeros = 0
tl zeros = zeros


record _≈_ {A} (xs : Stream A) (ys : Stream A) : Set where
  coinductive
  field
    hd-≡ : hd xs ≡ hd ys
    tl-≈ : tl xs ≈ tl ys

open _≈_

refl-≈ : {A : Set} -> {s : Stream A} -> s ≈ s
hd-≡ (refl-≈ {_} {s}) = refl
tl-≈ (refl-≈ {_} {s}) = refl-≈ {_} {tl s}

trans-≈ : {A : Set} -> {x y z : Stream A} -> x ≈ y -> y ≈ z -> x ≈ z
hd-≡ (trans-≈ p q) = trans (hd-≡ p) (hd-≡ q)
tl-≈ (trans-≈ p q) = trans-≈ (tl-≈ p) (tl-≈ q)

≡to≈ : {A : Set} -> {x y : Stream A} -> x ≡ y -> x ≈ y
≡to≈ refl = refl-≈

cong-≈ : {A B : Set} -> {x y : A} -> (f : A -> Stream B) -> x ≡ y -> f x ≈ f y
hd-≡ (cong-≈ f p) = cong (λ x -> hd (f x)) p
tl-≈ (cong-≈ f p) = cong-≈ tl (cong f p)

pos : {A : Set} -> Nat -> Stream A -> A
pos 0 x = hd x
pos (suc n) x = pos n (tl x)

natS : Nat -> Stream Nat
hd (natS n) = n
tl (natS n) = natS (suc n)


tailn : {A : Set} -> (n : Nat) -> Stream A -> Stream A
tailn 0 x = x
tailn (suc n) x = tl (tailn n x)


tailNatS : (n : Nat) -> tailn n (natS 0) ≈ natS n
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

posNatS2 : (n m : Nat) -> pos n (tl (natS m)) ≡ suc (pos n (natS m))
posNatS2 0 m = refl
posNatS2 (suc n) m = posNatS2 n (suc m)



posNatS : (m n : Nat) -> pos (suc n) (natS m) ≡ pos n (natS (suc m))
posNatS n m = refl



posNatS+ : (n m : Nat) -> pos n (natS m) ≡ n + m
posNatS+ 0 m = refl
posNatS+ (suc n) m  = trans (posNatS2 n m) (cong suc (posNatS+ n m))


