open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
tet : (i j : Level) → Set (i ⊔ j) ≡ Set (j ⊔ i)
tet i j = refl
