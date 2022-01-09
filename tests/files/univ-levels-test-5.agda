open import Agda.Primitive
open import Agda.Builtin.Equality
tet2 : (i j : Level) -> Set ((lsuc i) ⊔ (lsuc j))
tet2 i j = Set (i ⊔ j)
