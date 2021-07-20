require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

constant symbol tet2 : El setω (∀ (λ i, setω) (λ i, ∀ (λ j, set ((s 0ₙ z) ⊕ ((s (sₙ 0ₙ) (i ⊕ z)) ⊕ (s (sₙ 0ₙ) (j ⊕ z))))) (λ j, ⋄ (set ((s 0ₙ z) ⊕ ((s 0ₙ (i ⊕ z)) ⊕ (s 0ₙ (j ⊕ z))))))));

