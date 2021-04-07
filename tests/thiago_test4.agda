open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
tet3 : Set (lsuc lzero)
tet3 = (λ i j → Set (i ⊔ j)) lzero lzero
