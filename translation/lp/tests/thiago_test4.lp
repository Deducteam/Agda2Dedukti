require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Primitive as Agda__Primitive;
symbol tet3 : El (set (s (sₙ (sₙ 0ₙ)) z)) (⋄ (set (s (sₙ 0ₙ) z)));
rule tet3 ↪ ⋄ (set (s 0ₙ (Agda__Primitive.lzero ⊕ z)));
 
