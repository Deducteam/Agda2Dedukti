open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Primitive
open import Agda.Builtin.Size


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


data Bisim {a} {b} {A : Set a} {B : Set b} :
           Colist A -> Colist B -> Set (a ⊔ b) where
  []  : Bisim [] []
  _∷_ : ∀ {x y xs ys} → x \equiv y → Thunk^R Bisim xs ys →
        Bisim (x ∷ xs) (y ∷ ys)




