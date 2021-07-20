require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

constant symbol TYPE__Lift : Π a : L, Π {|!ℓ|} : L, Π A : El (set (s (sₙ 0ₙ) (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))), TYPE;
constant symbol Lift : El setω (∀ (λ a, setω) (λ a, ∀ (λ {|!ℓ|}, set ((s 0ₙ z) ⊕ ((s (sₙ 0ₙ) (a ⊕ z)) ⊕ (s (sₙ 0ₙ) ({|!ℓ|} ⊕ z))))) (λ {|!ℓ|}, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set ((s 0ₙ z) ⊕ ((s (sₙ 0ₙ) (a ⊕ z)) ⊕ (s (sₙ 0ₙ) ({|!ℓ|} ⊕ z))))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⋄ (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s 0ₙ ({|!ℓ|} ⊕ z))))))))));
rule El _ (Lift $a ${|!ℓ|} $A) ↪ TYPE__Lift $a ${|!ℓ|} $A;
constant symbol Lift__lift : El setω (∀ (λ a, setω) (λ a, ∀ (λ {|!ℓ|}, set ((s 0ₙ z) ⊕ ((s (sₙ 0ₙ) (a ⊕ z)) ⊕ (s 0ₙ ({|!ℓ|} ⊕ z))))) (λ {|!ℓ|}, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s 0ₙ ({|!ℓ|} ⊕ z))))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⇝ (set (s 0ₙ (a ⊕ z))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s 0ₙ ({|!ℓ|} ⊕ z))))) A (λ _0, (Lift a {|!ℓ|} A)))))));
rule η _ (Lift _ _ _) (Lift__lift $a ${|!ℓ|} $A $x) ↪ Lift__lift $a ${|!ℓ|} $A (η (s 0ₙ ($a ⊕ z)) $A $x);
 

symbol lower : El setω (∀ (λ a, setω) (λ a, ∀ (λ {|!ℓ|}, set ((s 0ₙ z) ⊕ ((s (sₙ 0ₙ) (a ⊕ z)) ⊕ (s 0ₙ ({|!ℓ|} ⊕ z))))) (λ {|!ℓ|}, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s 0ₙ ({|!ℓ|} ⊕ z))))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⇝ (set ((s 0ₙ z) ⊕ ((s 0ₙ (a ⊕ z)) ⊕ (s 0ₙ ({|!ℓ|} ⊕ z))))) (set (s 0ₙ (a ⊕ z))) (Lift a {|!ℓ|} A) (λ _0, A))))));
rule lower $a ${|!ℓ|} $A (Lift__lift _ _ _ $x) ↪ η (s 0ₙ ($a ⊕ z)) $A $x;
 
