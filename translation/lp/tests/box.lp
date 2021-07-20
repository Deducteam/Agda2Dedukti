require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

constant symbol TYPE__Box : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol Box : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⋄ (set (s 0ₙ z)))));
rule El _ (Box $A) ↪ TYPE__Box $A;
constant symbol Box__inside : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, (Box A)))));
rule η _ (Box _) (Box__inside $A $x) ↪ Box__inside $A (η (s 0ₙ z) $A $x);
 

symbol openBox : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Box A) (λ _0, A))));
rule openBox $A (Box__inside _ $x) ↪ η (s 0ₙ z) $A $x;
 
