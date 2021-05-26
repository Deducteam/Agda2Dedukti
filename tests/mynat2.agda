data N : Set where
  zero : N
  suc : N -> N

data Eq {A : Set} : A → A → Set where
 refl : {a : A} → Eq a a

cong : {x y : N} → (Eq x y) → (f : N → N) → (Eq (f x) (f y))
cong refl f = refl


sum : N → N → N
sum zero y = y
sum (suc x) y = suc (sum x y)

sum0 : (x : N) → (Eq x (sum x zero))
sum0 zero = refl
sum0 (suc x) = cong (sum0 x) suc



  
