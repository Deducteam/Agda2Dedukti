open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
tet2 : (i j : Level) -> Set ((lsuc i) ⊔ (lsuc j))
tet2 i j = Set (i ⊔ j)
