data N : Set where
  zero : N
  suc : N -> N

data Eq {A : Set} : A → A → Set where
 refl : {a : A} → Eq a a

data false : Set where

-- zero is no successor --
suc0 : (x : N) → Eq (suc x) zero → false
suc0 x ()

--sum : N → N → N
--sum zero y = y
--sum (suc x) y = suc (sum x y)



  
