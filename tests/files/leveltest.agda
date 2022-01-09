open import Agda.Primitive

id : (i : Level) → (A : Set i) → A → A
id _ = λ A x → x

