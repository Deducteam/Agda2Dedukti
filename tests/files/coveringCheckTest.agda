open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

tr : Nat -> Nat
tr 0 = 0
tr (suc x) = 0
--tr _ = 2

trr : Nat -> Nat -> Nat
trr 0 3 = 1
trr 0 _ = 2
trr _ _ = 3
