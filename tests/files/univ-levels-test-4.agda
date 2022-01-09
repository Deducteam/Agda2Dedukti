open import Agda.Primitive
open import Agda.Builtin.Equality
tet3 : Set (lsuc lzero)
tet3 = (λ i j → Set (i ⊔ j)) lzero lzero
