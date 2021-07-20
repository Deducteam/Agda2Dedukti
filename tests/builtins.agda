open import Agda.Builtin.Sigma

Pair : (A B : Set) -> Set
Pair A B = Σ A (λ _ → B)
