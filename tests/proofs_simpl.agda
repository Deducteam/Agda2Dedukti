
data _≡_ {A : Set} : A -> A -> Set where
  refl : {x : A} -> x ≡ x

trans : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans p refl = p

cong : {A B : Set} -> {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

