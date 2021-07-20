open import Agda.Primitive
comp : ((i : Level) → Set i → Set i) → ((i : Level) → Set i) → (i : Level) → Set i
comp f a i = (f i) (a i)
