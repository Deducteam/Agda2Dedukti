module coind_old2 where

open import Agda.Builtin.Coinduction
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality



data Stream : Set where
   cons  : Nat → ∞ Stream → Stream


zeros : Stream
zeros = cons 0 (♯ zeros)

tail : Stream → Stream
tail (cons v s) = ♭ s

head : Stream → Nat
head (cons v s) = v

proof : head (tail zeros) ≡ 0
proof = refl




