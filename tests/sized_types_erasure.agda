open import Agda.Builtin.Bool
open import Agda.Builtin.List

boolOr : Bool -> Bool -> Bool
boolOr true _ = true
boolOr false b = b

boolAnd : Bool -> Bool -> Bool
boolAnd true b = b
boolAnd false b = false

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y


record Lang (A : Set) : Set where
  coinductive
  field
    ν : Bool
    δ : A → Lang A

open Lang
{-# TERMINATING #-}
∅ : ∀ {A}  → Lang A
ν ∅   = false
δ ∅ _ = ∅

{-# TERMINATING #-}
ε : ∀ {A} → Lang A
ν ε   = true
δ ε _ = ∅

{-# TERMINATING #-}
_+_ : ∀ {A} → Lang A → Lang A → Lang A
ν (a + b)   = boolOr (ν a) (ν b)
δ (a + b) x = δ a x + δ b x

infixl 10 _+_

{-# TERMINATING #-}
_·_ : ∀ {A} → Lang A → Lang A → Lang A
ν (a · b)   = boolAnd (ν a) (ν b)
δ (a · b) x = if (ν a) then (δ a x · b + δ b x) else (δ a x · b)

{-# TERMINATING #-}
_* : ∀ {A} → Lang A → Lang A
ν (a *)   = true
δ (a *) x = δ a x · a *

infixl 30 _*

infixl 20 _·_

_∈_ : ∀ {A} → List A → Lang A → Bool
[]      ∈ a = ν a
(x ∷ w) ∈ a = w ∈ δ a x

