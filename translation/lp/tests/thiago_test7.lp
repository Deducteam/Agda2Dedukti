require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Primitive as Agda__Primitive;
symbol tet : El (set (s (sₙ (sₙ 0ₙ)) z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ (sₙ 0ₙ)) z)) Agda__Primitive.Level (λ i, (⋄ (set (s (sₙ 0ₙ) z)))));
rule tet $i ↪ ⋄ (set (s 0ₙ z));
 
