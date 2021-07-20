require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

constant symbol A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));

constant symbol B : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));

constant symbol {|!TYPE___≡_|} : Π S : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π _0 : El (set (s 0ₙ z)) S, Π _0 : El (set (s 0ₙ z)) S, TYPE;
constant symbol {|!_≡_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ S, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) S (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) S (λ _0, (⋄ (set (s 0ₙ z)))))))));
rule El _ ({|!_≡_|} $S $x0 $x) ↪ {|!TYPE___≡_|} $S (η (s 0ₙ z) $S $x0) (η (s 0ₙ z) $S $x);
constant symbol {|!_≡___refl|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ S, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) S (λ a, ({|!_≡_|} S (η (s 0ₙ z) S a) (η (s 0ₙ z) S a))))));
rule η _ ({|!_≡_|} _ _ _) ({|!_≡___refl|} $S $a) ↪ {|!_≡___refl|} $S (η (s 0ₙ z) $S $a);
 

symbol cong : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, B)) (λ f, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≡_|} A (η (s 0ₙ z) A x) (η (s 0ₙ z) A y)) (λ _0, ({|!_≡_|} B (η (s 0ₙ z) B (f (η (s 0ₙ z) A x))) (η (s 0ₙ z) B (f (η (s 0ₙ z) A y))))))))))))))));
rule cong $A $B $x _ $f ({|!_≡___refl|} _ _) ↪ η (s 0ₙ z) ({|!_≡_|} $B (η (s 0ₙ z) $B ($f (η (s 0ₙ z) $A $x))) (η (s 0ₙ z) $B ($f (η (s 0ₙ z) $A $x)))) ({|!_≡___refl|} $B (η (s 0ₙ z) $B ($f (η (s 0ₙ z) $A $x))));
 
