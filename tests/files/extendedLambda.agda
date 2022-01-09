open import Agda.Builtin.Nat

record Pair : Set where
  field
    fst : Nat
    snd : Nat
open Pair

bla : Pair
bla = λ where .fst → 4
              .snd → 2


bla2 : Pair
bla2 = λ where .fst → 1
               .snd → 0
