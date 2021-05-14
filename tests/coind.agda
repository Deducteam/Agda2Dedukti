open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

record Stream : Set where
  coinductive
  field
    hd : Nat
    tl : Stream

even : Stream → Stream
Stream.hd (even xs) = Stream.hd xs
Stream.tl (even xs) = even (Stream.tl (Stream.tl xs))

ones : Stream
Stream.hd ones = 1
Stream.tl ones = ones
