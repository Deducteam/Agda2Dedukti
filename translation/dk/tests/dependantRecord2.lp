require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

constant symbol {|TYPE__Σ|} : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π B : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z))))), TYPE;
constant symbol {|Σ|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z))))) (λ B, (⋄ (set (s 0ₙ z)))))));
rule El _ ({|Σ|} $A $B) ↪ {|TYPE__Σ|} $A $B;
constant symbol {|Σ'constructor|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z))))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ fst, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (B fst) (λ snd, ({|Σ|} A B)))))))));
symbol {|Σ__fst|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z))))) (λ B, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) ({|Σ|} A B) (λ r, A))))));
symbol {|Σ__snd|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z))))) (λ B, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) ({|Σ|} A B) (λ r, (B ({|Σ__fst|} A B r))))))));


rule {|Σ__fst|} $A $B ({|Σ'constructor|} $A $B $fst $snd) ↪ $fst;
 
rule {|Σ__snd|} $A $B ({|Σ'constructor|} $A $B $fst $snd) ↪ $snd;
 
