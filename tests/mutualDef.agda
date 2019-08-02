open import Agda.Builtin.Nat

f : Nat -> Nat
g : Nat -> Nat

f = g
g 0 = 0
g (suc x) = f x
