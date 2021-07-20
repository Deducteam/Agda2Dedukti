require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

constant symbol TYPE__N : TYPE;
constant symbol N : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ N ↪ TYPE__N;
constant symbol N__zero : El (set (s 0ₙ z)) N;
constant symbol N__suc : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N));
rule η _ N N__zero ↪ N__zero;
rule η _ N (N__suc $x) ↪ N__suc (η (s 0ₙ z) N $x);
 


constant symbol TYPE__Eq : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π _0 : El (set (s 0ₙ z)) A, Π _0 : El (set (s 0ₙ z)) A, TYPE;
constant symbol Eq : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z)))))))));
rule El _ (Eq $A $x0 $x) ↪ TYPE__Eq $A (η (s 0ₙ z) $A $x0) (η (s 0ₙ z) $A $x);
constant symbol Eq__refl : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, (Eq A (η (s 0ₙ z) A a) (η (s 0ₙ z) A a))))));
rule η _ (Eq _ _ _) (Eq__refl $A $a) ↪ Eq__refl $A (η (s 0ₙ z) $A $a);
 

constant symbol TYPE__false : TYPE;
constant symbol false : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ false ↪ TYPE__false;

symbol suc0 : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Eq N (η (s 0ₙ z) N (N__suc (η (s 0ₙ z) N x))) (η (s 0ₙ z) N N__zero)) (λ _0, false))));

