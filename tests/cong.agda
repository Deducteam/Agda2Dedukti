variable 
  A : Set
  B : Set

data _≡_ {S : Set} : S -> S -> Set where
  refl : {a : S} -> a ≡ a
infix 4 _≡_

cong : {x y : A} → {f : A → B} → x ≡ y → f x ≡ f y
cong refl = refl
