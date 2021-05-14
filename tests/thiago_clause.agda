open import Agda.Builtin.Nat

max : Nat → Nat → Nat
max 0 0 = 0
max x 0 = x
max 0 x = x
max (suc x) (suc y) = suc (max x y)
