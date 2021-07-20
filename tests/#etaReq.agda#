open import Agda.Builtin.Nat

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a
infix 4 _≡_

record Box : Set where
  constructor cons
  field openBox : Nat

b1 : Box
b1 = cons 3

b2 = cons 3

p : b1 ≡ b2
p = refl

record Box' : Set where
  constructor cons'
  no-eta-equality
  field openBox' : Nat

b1' = record {openBox' = 3}

b2' = record {openBox' = 3}

p' : b1' ≡ b2'
p' = refl

record Unit : Set where


pro : (x y : Unit) -> x ≡ y
pro _ _ = refl



