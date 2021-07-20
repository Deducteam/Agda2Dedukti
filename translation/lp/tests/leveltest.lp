require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

symbol id : El setω (∀ (λ i, set (s (sₙ 0ₙ) (i ⊕ z))) (λ i, ⇝ (set (s (sₙ 0ₙ) (i ⊕ z))) (set (s 0ₙ (i ⊕ z))) (⋄ (set (s 0ₙ (i ⊕ z)))) (λ A, (⇝ (set (s 0ₙ (i ⊕ z))) (set (s 0ₙ (i ⊕ z))) A (λ _0, A)))));
rule id $i $A $x ↪ η (s 0ₙ ($i ⊕ z)) $A $x;
 
