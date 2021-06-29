data N : Set where
  zero : N
  suc : N → N

data Neq : N → N → Set where
  refl : (x : N) → Neq x x

-- equality is a congruence --
cong : {x y : N} → (Neq x y) → (f : N → N) → (Neq (f x) (f y))
cong (refl a) f = refl (f a)
