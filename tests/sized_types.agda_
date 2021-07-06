{-# OPTIONS --sized-types --guardedness #-}
open import Agda.Builtin.Size
open import Agda.Builtin.Bool

_∨_ : Bool → Bool → Bool
infixl 20 _∨_
true ∨ _ = true
false ∨ b = b

_∧_ : Bool → Bool → Bool
infixl 20 _∧_
true  ∧ b = b
false ∧ _ = false

if_then_else : ∀{A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

record Lang (i : Size) (A : Set) : Set where
  coinductive
  field
    ν : Bool
    δ : ∀{j : Size< i} → A → Lang j A
open Lang

∅ : ∀ {i A}  → Lang i A
ν ∅   = false
δ ∅ _ = ∅

ε : ∀ {i A} → Lang i A
ν ε   = true
δ ε _ = ∅

_+_ : ∀ {i A} → Lang i A → Lang i A → Lang i A
ν (a + b)   = ν a   ∨ ν b
δ (a + b) x = δ a x + δ b x

infixl 10 _+_


_·_ : ∀ {i A} → Lang i A → Lang i A → Lang i A
ν (a · b)   = ν a ∧ ν b
δ (a · b) x = if (ν a) then (((δ a x) · b) + δ b x) else (δ a x · b)

infixl 20 _·_

_* : ∀ {i A} → Lang i A → Lang i A
ν (a *)   = true
δ (a *) x = δ a x · a *

infixl 30 _*

