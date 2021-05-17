open import Agda.Primitive
open import Agda.Builtin.Equality
tet : (i j : Level) → Set (i ⊔ j) ≡ Set (j ⊔ i)
tet i j = refl
