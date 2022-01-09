open import Agda.Primitive
open import Agda.Builtin.Equality
tet : (i j : Level) → i ⊔ j ≡ j ⊔ i
tet i j = refl
