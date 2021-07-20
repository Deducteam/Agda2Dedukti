{-# OPTIONS --guardedness #-}
open import Agda.Builtin.Coinduction
open import Agda.Builtin.Nat

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

zeros : Stream Nat
zeros = 0 ∷ (♯ zeros)

natStream : Nat → Stream Nat
natStream n = n ∷ (♯ (natStream (suc n)))



