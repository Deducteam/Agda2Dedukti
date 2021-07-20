require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Sigma as Agda__Builtin__Sigma;
symbol Pair : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ B, (⋄ (set (s 0ₙ z)))))));
rule Pair $A $B ↪ Agda__Builtin__Sigma.{|!Σ|} (s 0ₙ z) (s 0ₙ z) $A (λ _0, $B);
 
