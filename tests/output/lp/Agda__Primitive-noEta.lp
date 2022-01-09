require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

symbol Set : El (set (s (sₙ (sₙ 0ₙ)) z)) (⋄ (set (s (sₙ 0ₙ) z)));

symbol Prop : El (set (s (sₙ (sₙ 0ₙ)) z)) (⋄ (set (s (sₙ 0ₙ) z)));


constant symbol Level : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ Level ↪ L;

symbol lzero : El (set (s 0ₙ z)) Level;
rule lzero ↪ s 0ₙ z;

symbol lsuc : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Level (λ {|!ℓ|}, Level));
rule lsuc ↪ s (sₙ 0ₙ);

symbol {|!_⊔_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Level (λ {|!ℓ₁|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Level (λ {|!ℓ₂|}, Level))));
rule {|!_⊔_|} ↪ λ x y, x ⊕ y;

