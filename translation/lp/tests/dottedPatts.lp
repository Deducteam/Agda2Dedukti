require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

constant symbol TYPE__N : TYPE;
constant symbol N : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ N ↪ TYPE__N;
constant symbol N__zero : El (set (s 0ₙ z)) N;
constant symbol N__suc : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N));



constant symbol TYPE__Neq : Π _0 : El (set (s 0ₙ z)) N, Π _0 : El (set (s 0ₙ z)) N, TYPE;
constant symbol Neq : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) N (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) N (λ _0, (⋄ (set (s 0ₙ z)))))));
rule El _ (Neq $x0 $x) ↪ TYPE__Neq $x0 $x;
constant symbol Neq__refl : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (Neq x x)));


symbol cong : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Neq x y) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N)) (λ f, (Neq (f x) (f y))))))))));
rule cong $x _ (Neq__refl _) $f ↪ Neq__refl ($f $x);
 
