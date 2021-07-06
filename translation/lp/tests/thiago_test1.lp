require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

symbol idpoly : El setω (∀ (λ n, set (s (sₙ 0ₙ) (n ⊕ z))) (λ n, ⇝ (set (s (sₙ 0ₙ) (n ⊕ z))) (set (s 0ₙ (n ⊕ z))) (⋄ (set (s 0ₙ (n ⊕ z)))) (λ A, (⇝ (set (s 0ₙ (n ⊕ z))) (set (s 0ₙ (n ⊕ z))) A (λ _0, A)))));
rule idpoly $n $A $x ↪ $x;
 
