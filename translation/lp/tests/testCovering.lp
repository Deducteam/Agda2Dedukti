require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

constant symbol TYPE__N : TYPE;
constant symbol N : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ N ↪ TYPE__N;
constant symbol N__zero : El (set (s 0ₙ z)) N;
constant symbol N__suc : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N));
rule η _ N N__zero ↪ N__zero;
rule η _ N (N__suc $x) ↪ N__suc (η (s 0ₙ z) N $x);
 


symbol max : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N))));
rule max N__zero $x ↪ η (s 0ₙ z) N $x;
rule max (N__suc $x) N__zero ↪ η (s 0ₙ z) N (N__suc (η (s 0ₙ z) N $x));
rule max (N__suc $x0) (N__suc $x) ↪ η (s 0ₙ z) N (N__suc (η (s 0ₙ z) N (max (η (s 0ₙ z) N $x0) (η (s 0ₙ z) N $x))));
 
