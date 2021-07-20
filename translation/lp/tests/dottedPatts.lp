require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

constant symbol TYPE__N : TYPE;
constant symbol N : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ N ↪ TYPE__N;
constant symbol N__zero : El (set (s 0ₙ z)) N;
constant symbol N__suc : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N));
rule η _ N N__zero ↪ N__zero;
rule η _ N (N__suc $x) ↪ N__suc (η (s 0ₙ z) N $x);
 


constant symbol TYPE__Neq : Π _0 : El (set (s 0ₙ z)) N, Π _0 : El (set (s 0ₙ z)) N, TYPE;
constant symbol Neq : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) N (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) N (λ _0, (⋄ (set (s 0ₙ z)))))));
rule El _ (Neq $x0 $x) ↪ TYPE__Neq (η (s 0ₙ z) N $x0) (η (s 0ₙ z) N $x);
constant symbol Neq__refl : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (Neq (η (s 0ₙ z) N x) (η (s 0ₙ z) N x))));
rule η _ (Neq _ _) (Neq__refl $x) ↪ Neq__refl (η (s 0ₙ z) N $x);
 

symbol cong : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Neq (η (s 0ₙ z) N x) (η (s 0ₙ z) N y)) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N)) (λ f, (Neq (η (s 0ₙ z) N (f (η (s 0ₙ z) N x))) (η (s 0ₙ z) N (f (η (s 0ₙ z) N y))))))))))));
rule cong $x _ (Neq__refl _) $f ↪ η (s 0ₙ z) (Neq (η (s 0ₙ z) N ($f (η (s 0ₙ z) N $x))) (η (s 0ₙ z) N ($f (η (s 0ₙ z) N $x)))) (Neq__refl (η (s 0ₙ z) N ($f (η (s 0ₙ z) N $x))));
 
