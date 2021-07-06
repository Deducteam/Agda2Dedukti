require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

symbol Set : El (set (s (sₙ (sₙ 0ₙ)) z)) (⋄ (set (s (sₙ 0ₙ) z)));

symbol Prop : El (set (s (sₙ (sₙ 0ₙ)) z)) (⋄ (set (s (sₙ 0ₙ) z)));


constant symbol Level : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ Level ↪ L;

