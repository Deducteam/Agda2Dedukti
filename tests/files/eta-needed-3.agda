open import Agda.Builtin.Nat

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a
infix 4 _≡_


record Unit : Set where
-- uncommenting the following line breaks the proofs
--  no-eta-equality

pro : (x y : Unit) -> x ≡ y
pro _ _ = refl

data Uni : Set where
  I : Uni

--pro' : (x y : Uni) → x ≡ y
--pro' _ _ = refl

