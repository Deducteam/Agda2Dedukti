open import Agda.Builtin.Nat

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a
infix 4 _≡_

record Box : Set where
  constructor cons
-- uncommenting the following line breaks the proofs
--  no-eta-equality
  field openBox : Nat

b1 : Box
Box.openBox b1 = 3

b2 : Box
b2 = cons 3

b2' : Box
b2' = record {openBox = 3}

b3 : Box
Box.openBox b3 = 3

b4 : Box
b4 = λ where .Box.openBox → 3

b5 : Box
b5 = λ where .Box.openBox → 3

p : b1 ≡ b2
p = refl

p' : b2' ≡ b2
p' = refl

p2 : b3 ≡ b1
p2 = refl

p3 : b1 ≡ b5
p3 = refl

p4 : b4 ≡ b5
p4 = refl

record Nat2 : Set where
  field a : Nat
  field b : Nat
