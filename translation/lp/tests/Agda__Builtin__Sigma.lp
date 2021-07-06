require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

constant symbol {|!TYPE__Σ|} : Π a : L, Π b : L, Π A : El (set (s (sₙ 0ₙ) (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))), Π B : El (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s (sₙ 0ₙ) (b ⊕ z))))) (⇝ (set (s 0ₙ (a ⊕ z))) (set (s (sₙ 0ₙ) (b ⊕ z))) A (λ _0, (⋄ (set (s 0ₙ (b ⊕ z)))))), TYPE;
constant symbol {|!Σ|} : El setω (∀ (λ a, setω) (λ a, ∀ (λ b, set ((s 0ₙ z) ⊕ ((s (sₙ 0ₙ) (a ⊕ z)) ⊕ (s (sₙ 0ₙ) (b ⊕ z))))) (λ b, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set ((s 0ₙ z) ⊕ ((s (sₙ 0ₙ) (a ⊕ z)) ⊕ (s (sₙ 0ₙ) (b ⊕ z))))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⇝ (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s (sₙ 0ₙ) (b ⊕ z))))) (set ((s 0ₙ z) ⊕ ((s (sₙ 0ₙ) (a ⊕ z)) ⊕ (s (sₙ 0ₙ) (b ⊕ z))))) (⇝ (set (s 0ₙ (a ⊕ z))) (set (s (sₙ 0ₙ) (b ⊕ z))) A (λ _0, (⋄ (set (s 0ₙ (b ⊕ z)))))) (λ B, (⋄ (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s 0ₙ (b ⊕ z))))))))))));
rule El _ ({|!Σ|} $a $b $A $B) ↪ {|!TYPE__Σ|} $a $b $A $B;
symbol {|!Σ__fst|} : El setω (∀ (λ a, setω) (λ a, ∀ (λ b, set ((s 0ₙ z) ⊕ ((s (sₙ 0ₙ) (a ⊕ z)) ⊕ (s (sₙ 0ₙ) (b ⊕ z))))) (λ b, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s (sₙ 0ₙ) (b ⊕ z))))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⇝ (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s (sₙ 0ₙ) (b ⊕ z))))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s 0ₙ (b ⊕ z))))) (⇝ (set (s 0ₙ (a ⊕ z))) (set (s (sₙ 0ₙ) (b ⊕ z))) A (λ _0, (⋄ (set (s 0ₙ (b ⊕ z)))))) (λ B, (⇝proj (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s 0ₙ (b ⊕ z))))) (set (s 0ₙ (a ⊕ z))) ({|!Σ|} a b A B) (λ r, A))))))));
symbol {|!Σ__snd|} : El setω (∀ (λ a, setω) (λ a, ∀ (λ b, set ((s 0ₙ z) ⊕ ((s (sₙ 0ₙ) (a ⊕ z)) ⊕ (s (sₙ 0ₙ) (b ⊕ z))))) (λ b, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s (sₙ 0ₙ) (b ⊕ z))))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⇝ (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s (sₙ 0ₙ) (b ⊕ z))))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s 0ₙ (b ⊕ z))))) (⇝ (set (s 0ₙ (a ⊕ z))) (set (s (sₙ 0ₙ) (b ⊕ z))) A (λ _0, (⋄ (set (s 0ₙ (b ⊕ z)))))) (λ B, (⇝proj (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s 0ₙ (b ⊕ z))))) (set (s 0ₙ (b ⊕ z))) ({|!Σ|} a b A B) (λ r, (B ({|!Σ__fst|} a b A B r))))))))));
constant symbol {|!_,_|} : El setω (∀ (λ a, setω) (λ a, ∀ (λ b, set ((s 0ₙ z) ⊕ ((s (sₙ 0ₙ) (a ⊕ z)) ⊕ (s (sₙ 0ₙ) (b ⊕ z))))) (λ b, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s (sₙ 0ₙ) (b ⊕ z))))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⇝ (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s (sₙ 0ₙ) (b ⊕ z))))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s 0ₙ (b ⊕ z))))) (⇝ (set (s 0ₙ (a ⊕ z))) (set (s (sₙ 0ₙ) (b ⊕ z))) A (λ _0, (⋄ (set (s 0ₙ (b ⊕ z)))))) (λ B, (⇝ (set (s 0ₙ (a ⊕ z))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s 0ₙ (b ⊕ z))))) A (λ fst, (⇝ (set (s 0ₙ (b ⊕ z))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s 0ₙ (b ⊕ z))))) (B fst) (λ snd, ({|!Σ|} a b A B)))))))))));

rule {|!Σ__fst|} $a $b $A $B ({|!_,_|} _ _ _ _ $fst $snd) ↪ $fst;
 
rule {|!Σ__snd|} $a $b $A $B ({|!_,_|} _ _ _ _ $fst $snd) ↪ $snd;
 

