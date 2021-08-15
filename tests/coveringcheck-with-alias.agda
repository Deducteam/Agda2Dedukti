open import Agda.Builtin.Nat

record Box : Set where
  constructor cons
  field openBox : Nat

b1 : Box
b1 = cons 3

b2 = cons 3


