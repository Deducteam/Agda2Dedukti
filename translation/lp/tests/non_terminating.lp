require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

symbol f : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, A));
rule f $A ↪ η (s 0ₙ z) $A (f $A);
 
