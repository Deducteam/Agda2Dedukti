open import Agda.Primitive
open import Agda.Builtin.Equality

idpoly : (n : Level) → (A : Set n) → A → A
idpoly n A a = a
