module lift where

open import Agda.Primitive

data Lift {a} ℓ (A : Set a) : Set (a ⊔ ℓ) where
  lift : A → Lift ℓ A

lower : ∀ {a} ℓ (A : Set a) → Lift ℓ A → Lift ℓ A

lower ℓ A (lift x) = lift x
