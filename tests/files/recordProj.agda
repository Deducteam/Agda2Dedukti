open import Agda.Builtin.Nat
open import Agda.Builtin.Equality


record Rec {A : Set} {B : Set} : Set where
  constructor cons
  field a : A
  field b : B

rec : Rec
rec = cons 3 5

equality : (Rec.a rec) ≡ 3
equality = refl



