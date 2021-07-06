require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Equality as Agda__Builtin__Equality;
require tests.Agda__Primitive as Agda__Primitive;
symbol tet : El (set (s 0ₙ z)) (∀ (λ i, set (s 0ₙ z)) (λ i, ∀ (λ j, set (s 0ₙ z)) (λ j, Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Primitive.Level (Agda__Primitive.{|!_⊔_|} i j) (Agda__Primitive.{|!_⊔_|} j i))));
rule tet $i $j ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Primitive.Level (Agda__Primitive.{|!_⊔_|} $i $j);
 
