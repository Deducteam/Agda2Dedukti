open import Agda.Builtin.Nat

record Pair (A B : Set) : Set where
  field
    fst : A
    snd : B

p23 : Pair Nat Nat
p23 = record { fst = 2; snd = 3 }

p34 : Pair Nat Nat
Pair.fst p34 = 3
Pair.snd p34 = 4

p56 : Pair Nat Nat
p56 .Pair.fst = 5
p56 .Pair.snd = 6

p78 : Pair Nat Nat
p78 = λ where
  .Pair.fst → 7
  .Pair.snd → 8

record Pair2 (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

p45 : Pair2 Nat Nat
p45 = 4 , 5


