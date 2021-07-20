require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

constant symbol {|!TYPE__∞|} : Π a : L, Π A : El (set (s (sₙ 0ₙ) (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))), TYPE;
constant symbol {|!∞|} : El setω (∀ (λ a, set (s (sₙ 0ₙ) (a ⊕ z))) (λ a, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set (s (sₙ 0ₙ) (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⋄ (set (s 0ₙ (a ⊕ z)))))));
rule El _ ({|!∞|} $a $A) ↪ {|!TYPE__∞|} $a $A;
rule η _ ({|!∞|} $a $A) $y ↪ $y;
 
constant symbol {|!♯_|} : El setω (∀ (λ a, set (s (sₙ 0ₙ) (a ⊕ z))) (λ a, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set (s 0ₙ (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⇝ (set (s 0ₙ (a ⊕ z))) (set (s 0ₙ (a ⊕ z))) A (λ _0, ({|!∞|} a A))))));

symbol {|!♭|} : El setω (∀ (λ a, set (s (sₙ 0ₙ) (a ⊕ z))) (λ a, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set (s 0ₙ (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⇝proj (set (s 0ₙ (a ⊕ z))) (set (s 0ₙ (a ⊕ z))) ({|!∞|} a A) (λ _0, A)))));
rule {|!♭|} $a $A ({|!♯_|} _ _ $x) ↪ η (s 0ₙ ($a ⊕ z)) $A $x;
 
