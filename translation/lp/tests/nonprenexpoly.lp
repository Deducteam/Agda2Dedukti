require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

symbol comp : El setω (⇝ setω setω (∀ (λ i, set (s (sₙ 0ₙ) (i ⊕ z))) (λ i, ⇝ (set (s (sₙ 0ₙ) (i ⊕ z))) (set (s (sₙ 0ₙ) (i ⊕ z))) (⋄ (set (s 0ₙ (i ⊕ z)))) (λ _0, (⋄ (set (s 0ₙ (i ⊕ z))))))) (λ _0, (⇝ setω setω (∀ (λ i, set (s (sₙ 0ₙ) (i ⊕ z))) (λ i, ⋄ (set (s 0ₙ (i ⊕ z))))) (λ _0, (∀ (λ i, set (s (sₙ 0ₙ) (i ⊕ z))) (λ i, ⋄ (set (s 0ₙ (i ⊕ z)))))))));
rule comp $x0 $x $i ↪ $x0 $i ($x $i);
 
