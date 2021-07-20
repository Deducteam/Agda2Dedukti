require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

constant symbol {|!TYPE__Σ|} : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π B : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z))))), TYPE;
constant symbol {|!Σ|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z))))) (λ B, (⋄ (set (s 0ₙ z)))))));
rule El _ ({|!Σ|} $A $B) ↪ {|!TYPE__Σ|} $A (λ _0, $B (η (s 0ₙ z) $A _0));
constant symbol {|!Σ'constructor|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z))))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ fst, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (B (η (s 0ₙ z) A fst)) (λ snd, ({|!Σ|} A (λ _0, B (η (s 0ₙ z) A _0)))))))))));
symbol {|!Σ__fst|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z))))) (λ B, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!Σ|} A (λ _0, B (η (s 0ₙ z) A _0))) (λ r, A))))));
symbol {|!Σ__snd|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z))))) (λ B, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!Σ|} A (λ _0, B (η (s 0ₙ z) A _0))) (λ r, (B (η (s 0ₙ z) A ({|!Σ__fst|} A (λ _0, B (η (s 0ₙ z) A _0)) r)))))))));

rule η _ ({|!Σ|} $A $B) $y ↪ {|!Σ'constructor|} $A (λ _0, $B (η (s 0ₙ z) $A _0)) (η (s 0ₙ z) $A ({|!Σ__fst|} $A (λ _0, $B (η (s 0ₙ z) $A _0)) $y)) (η (s 0ₙ z) ($B (η (s 0ₙ z) $A ({|!Σ__fst|} $A (λ _0, $B (η (s 0ₙ z) $A _0)) $y))) ({|!Σ__snd|} $A (λ _0, $B (η (s 0ₙ z) $A _0)) $y));
 
rule {|!Σ__fst|} $A $B ({|!Σ'constructor|} _ _ $fst $snd) ↪ η (s 0ₙ z) $A $fst;
 
rule {|!Σ__snd|} $A $B ({|!Σ'constructor|} _ _ $fst $snd) ↪ η (s 0ₙ z) ($B (η (s 0ₙ z) $A $fst)) $snd;
 
