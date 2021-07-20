require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Equality as Agda__Builtin__Equality;
require tests.Agda__Primitive as Agda__Primitive;
symbol tet : El (set (s 0ₙ z)) (∀ (λ i, set (s 0ₙ z)) (λ i, Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Primitive.Level i i));
rule tet $i ↪ η (s 0ₙ z) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Primitive.Level $i $i) (Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Primitive.Level $i);
 
