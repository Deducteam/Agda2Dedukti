{-# OPTIONS --guardedness #-}
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

data ⊥ : Set where

data ∨ (A B : Set) : Set where
  inl : A → ∨ A B
  inr : B → ∨ A B

record Node : Set where
      coinductive 
      field
        value : Nat
        edge  : Node

open Node 

g1 : Node
g2 : Node

value g1 = 1
edge  g1 = g2

value g2 = 1
edge  g2 = g1


g3 : Node

value g3 = 1
edge  g3 = g3

record Bissim (A B : Node) : Set where
       coinductive
       field
         eqv : value A ≡ value B
         eqt : Bissim (edge A) (edge B)
open Bissim

bis1 : Bissim g1 g3
bis2 : Bissim g2 g3

eqv bis1 = refl
eqt bis1 = bis2

eqv bis2 = refl
eqt bis2 = bis1
