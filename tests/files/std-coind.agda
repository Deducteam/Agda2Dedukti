{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Primitive


record Thunk {ℓ} (F : Set ℓ) : Set ℓ where
  coinductive
  field force : F
open Thunk public

data Colist {a} (A : Set a) : Set a where
  []  : Colist A
  _∷_ : A → Thunk (Colist A) → Colist A

{-# TERMINATING #-}
zeros : Colist Nat
zeros = 0 ∷ (\ where .force -> zeros)


Thunk^R : ∀ {f g r} {F : Set f} {G : Set g}
          (R : F → G → Set r)
          (tf : Thunk F) (tg : Thunk G) → Set r
Thunk^R R tf tg = Thunk (R (tf .force) (tg .force))




