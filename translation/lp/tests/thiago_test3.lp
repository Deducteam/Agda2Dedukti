require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Equality as Agda__Builtin__Equality;
symbol tet : El setω (∀ (λ i, setω) (λ i, ∀ (λ j, set ((s 0ₙ z) ⊕ ((s (sₙ (sₙ 0ₙ)) (i ⊕ z)) ⊕ (s (sₙ (sₙ 0ₙ)) (j ⊕ z))))) (λ j, Agda__Builtin__Equality.{|!_≡_|} ((s 0ₙ z) ⊕ ((s (sₙ (sₙ 0ₙ)) (i ⊕ z)) ⊕ (s (sₙ (sₙ 0ₙ)) (j ⊕ z)))) (⋄ (set ((s 0ₙ z) ⊕ ((s (sₙ 0ₙ) (i ⊕ z)) ⊕ (s (sₙ 0ₙ) (j ⊕ z)))))) (⋄ (set ((s 0ₙ z) ⊕ ((s 0ₙ (i ⊕ z)) ⊕ (s 0ₙ (j ⊕ z)))))) (⋄ (set ((s 0ₙ z) ⊕ ((s 0ₙ (i ⊕ z)) ⊕ (s 0ₙ (j ⊕ z)))))))));
rule tet $i $j ↪ Agda__Builtin__Equality.{|!_≡___refl|} ((s 0ₙ z) ⊕ ((s (sₙ (sₙ 0ₙ)) ($i ⊕ z)) ⊕ (s (sₙ (sₙ 0ₙ)) ($j ⊕ z)))) (⋄ (set ((s 0ₙ z) ⊕ ((s (sₙ 0ₙ) ($i ⊕ z)) ⊕ (s (sₙ 0ₙ) ($j ⊕ z)))))) (⋄ (set ((s 0ₙ z) ⊕ ((s 0ₙ ($i ⊕ z)) ⊕ (s 0ₙ ($j ⊕ z))))));
 
