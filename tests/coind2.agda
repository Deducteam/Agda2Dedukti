{-# OPTIONS --guardedness #-}

data _≡_ {A : Set} : A -> A -> Set where
  refl : {a : A} -> a ≡ a
infix 4 _≡_

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

infixl 6 _+_

_+_ : Nat -> Nat -> Nat
zero + x = x
(suc x) + y = suc (x + y)


trans : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans p refl = p

cong : {A B : Set} -> {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

+-assoc : (x y z : Nat) -> (x + y) + z ≡ x + (y + z)
+-assoc zero y z = refl
+-assoc (suc x) y z = cong suc (+-assoc x y z)


record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A

open Stream



record _≈_ {A} (xs : Stream A) (ys : Stream A) : Set where
  coinductive
  field
    hd-≡ : hd xs ≡ hd ys
    tl-≈ : tl xs ≈ tl ys

open _≈_

{-

zeros : Stream Nat
hd zeros = zero
tl zeros = zeros

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
pos zero x = hd x
pos (suc n) x = pos n (tl x)

natS : Nat -> Stream Nat
hd (natS n) = n
tl (natS n) = natS (suc n)


tailn : {A : Set} -> (n : Nat) -> Stream A -> Stream A
tailn zero x = x
tailn (suc n) x = tl (tailn n x)


tailNatS : (n : Nat) -> tailn n (natS zero) ≈ natS n
tailNatS zero = refl-≈

hd-≡ (tailNatS (suc n)) = hd-≡ (tl-≈ (tailNatS n))
tl-≈ (tailNatS (suc n)) = tl-≈ (tl-≈ (tailNatS n))

plusS : (n : Nat) -> Stream Nat -> Stream Nat
hd (plusS n x) = n + (hd x)
tl (plusS n x) = plusS n (tl x)

etaPlusS : (x : Stream Nat) -> x ≈ plusS zero x
hd-≡ (etaPlusS x) = refl
tl-≈ (etaPlusS x) = etaPlusS (tl x)

plusS+ : (n m : Nat) -> (x : Stream Nat) -> plusS (n + m) x ≈ plusS n (plusS m x)
hd-≡ (plusS+ n m x) = +-assoc n m (hd x)
tl-≈ (plusS+ n m x) = plusS+ n m (tl x)


posNatS2 : (n m : Nat) -> pos n (tl (natS m)) ≡ suc (pos n (natS m))
posNatS2 zero m = refl
posNatS2 (suc n) m = posNatS2 n (suc m)



posNatS : (m n : Nat) -> pos (suc n) (natS m) ≡ pos n (natS (suc m))
posNatS n m = refl



posNatS+ : (n m : Nat) -> pos n (natS m) ≡ n + m
posNatS+ zero m = refl
posNatS+ (suc n) m  = trans (posNatS2 n m) (cong suc (posNatS+ n m))


plusS : (n : Nat) -> Stream Nat -> Stream Nat
hd (plusS n x) = n + (hd x)
tl (plusS n x) = plusS n (tl x)

etaPlusS : (x : Stream Nat) -> x ≈ plusS zero x
hd-≡ (etaPlusS x) = refl
tl-≈ (etaPlusS x) = etaPlusS (tl x)



plusS+ : (n m : Nat) -> (x : Stream Nat) -> plusS (n + m) x ≈ plusS n (plusS m x)
hd-≡ (plusS+ n m x) = +-assoc n m (hd x)
tl-≈ (plusS+ n m x) = plusS+ n m (tl x)




-}
