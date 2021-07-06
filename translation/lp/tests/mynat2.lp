require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

constant symbol TYPE__N : TYPE;
constant symbol N : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ N ↪ TYPE__N;
constant symbol N__zero : El (set (s 0ₙ z)) N;
constant symbol N__suc : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N));



constant symbol TYPE__Eq : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π _0 : El (set (s 0ₙ z)) A, Π _0 : El (set (s 0ₙ z)) A, TYPE;
constant symbol Eq : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z)))))))));
rule El _ (Eq $A $x0 $x) ↪ TYPE__Eq $A $x0 $x;
constant symbol Eq__refl : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, (Eq A a a)))));


symbol cong : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Eq N x y) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N)) (λ f, (Eq N (f x) (f y))))))))));
rule cong $x _ (Eq__refl _ _) $f ↪ Eq__refl N ($f $x);
 
symbol sum : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N))));
rule sum N__zero $x ↪ $x;
rule sum (N__suc $x0) $x ↪ N__suc (sum $x0 $x);
 
symbol sum0 : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (Eq N x (sum x N__zero))));
rule sum0 N__zero ↪ Eq__refl N N__zero;
rule sum0 (N__suc $x) ↪ cong $x (sum $x N__zero) (sum0 $x) N__suc;
 
