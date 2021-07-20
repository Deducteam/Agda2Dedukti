require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

constant symbol {|!TYPE___≡_|} : Π a : L, Π A : El (set (s (sₙ 0ₙ) (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))), Π x : El (set (s 0ₙ (a ⊕ z))) A, Π _0 : El (set (s 0ₙ (a ⊕ z))) A, TYPE;
constant symbol {|!_≡_|} : El setω (∀ (λ a, set (s (sₙ 0ₙ) (a ⊕ z))) (λ a, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set (s (sₙ 0ₙ) (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⇝ (set (s 0ₙ (a ⊕ z))) (set (s (sₙ 0ₙ) (a ⊕ z))) A (λ x, (⇝ (set (s 0ₙ (a ⊕ z))) (set (s (sₙ 0ₙ) (a ⊕ z))) A (λ _0, (⋄ (set (s 0ₙ (a ⊕ z)))))))))));
rule El _ ({|!_≡_|} $a $A $x0 $x) ↪ {|!TYPE___≡_|} $a $A $x0 $x;
constant symbol {|!_≡___refl|} : El setω (∀ (λ a, set (s (sₙ 0ₙ) (a ⊕ z))) (λ a, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set (s 0ₙ (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⇝ (set (s 0ₙ (a ⊕ z))) (set (s 0ₙ (a ⊕ z))) A (λ x, ({|!_≡_|} a A x x))))));


