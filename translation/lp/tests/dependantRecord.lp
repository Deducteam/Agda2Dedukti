require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

constant symbol TYPE__r : TYPE;
constant symbol r : El (set (s (sₙ (sₙ 0ₙ)) z)) (⋄ (set (s (sₙ 0ₙ) z)));
rule El _ r ↪ TYPE__r;
symbol r__A : El (set (s (sₙ 0ₙ) z)) (⇝proj (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) r (λ r, (⋄ (set (s 0ₙ z)))));
symbol r__b : El (set (s (sₙ 0ₙ) z)) (⇝proj (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) r (λ r, (r__A r)));
constant symbol cons : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ b, r))));

rule r__A (cons $A $b) ↪ $A;
 
rule r__b (cons $A $b) ↪ $b;
 

