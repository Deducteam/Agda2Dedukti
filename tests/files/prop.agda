{-# OPTIONS --prop #-}

open import Agda.Builtin.Equality

data ⊥ : Prop where

record ⊤ : Prop where
  constructor tt
{-
absurd : (A : Set) → ⊥ → A
absurd A ()

only-one-absurdity : {A : Set} → (p q : ⊥) → absurd A p ≡ absurd A q
only-one-absurdity p q = refl
-}
