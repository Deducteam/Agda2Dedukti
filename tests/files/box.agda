
data Box {A : Set} : Set where
  inside : A -> Box

openBox : {A : Set} -> Box {A} -> A
openBox (inside a) = a
