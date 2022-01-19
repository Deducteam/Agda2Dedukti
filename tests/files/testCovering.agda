data N : Set where
  zero : N
  suc : N -> N

max : N → N → N
max zero z = z
max z zero = z
max (suc x) (suc y) = suc (max x y)
