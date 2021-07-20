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
 

symbol cong : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Eq N (η (s 0ₙ z) N x) (η (s 0ₙ z) N y)) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N)) (λ f, (Eq N (η (s 0ₙ z) N (f (η (s 0ₙ z) N x))) (η (s 0ₙ z) N (f (η (s 0ₙ z) N y))))))))))));
rule cong $x _ (Eq__refl _ _) $f ↪ η (s 0ₙ z) (Eq N (η (s 0ₙ z) N ($f (η (s 0ₙ z) N $x))) (η (s 0ₙ z) N ($f (η (s 0ₙ z) N $x)))) (Eq__refl N (η (s 0ₙ z) N ($f (η (s 0ₙ z) N $x))));
 
symbol sum : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N))));
rule sum N__zero $x ↪ η (s 0ₙ z) N $x;
rule sum (N__suc $x0) $x ↪ η (s 0ₙ z) N (N__suc (η (s 0ₙ z) N (sum (η (s 0ₙ z) N $x0) (η (s 0ₙ z) N $x))));
 
symbol sum0 : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (Eq N (η (s 0ₙ z) N x) (η (s 0ₙ z) N (sum (η (s 0ₙ z) N x) (η (s 0ₙ z) N N__zero))))));
rule sum0 N__zero ↪ η (s 0ₙ z) (Eq N (η (s 0ₙ z) N N__zero) (η (s 0ₙ z) N (sum (η (s 0ₙ z) N N__zero) (η (s 0ₙ z) N N__zero)))) (Eq__refl N (η (s 0ₙ z) N N__zero));
rule sum0 (N__suc $x) ↪ η (s 0ₙ z) (Eq N (η (s 0ₙ z) N (N__suc (η (s 0ₙ z) N $x))) (η (s 0ₙ z) N (sum (η (s 0ₙ z) N (N__suc (η (s 0ₙ z) N $x))) (η (s 0ₙ z) N N__zero)))) (cong (η (s 0ₙ z) N $x) (η (s 0ₙ z) N (sum (η (s 0ₙ z) N $x) (η (s 0ₙ z) N N__zero))) (η (s 0ₙ z) (Eq N (η (s 0ₙ z) N $x) (η (s 0ₙ z) N (sum (η (s 0ₙ z) N $x) (η (s 0ₙ z) N N__zero)))) (sum0 (η (s 0ₙ z) N $x))) (λ _0, η (s 0ₙ z) N (N__suc (η (s 0ₙ z) N _0))));
 
