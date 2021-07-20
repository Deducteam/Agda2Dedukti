require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

constant symbol {|!TYPE___≡_|} : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π _0 : El (set (s 0ₙ z)) A, Π _0 : El (set (s 0ₙ z)) A, TYPE;
constant symbol {|!_≡_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z)))))))));
rule El _ ({|!_≡_|} $A $x0 $x) ↪ {|!TYPE___≡_|} $A (η (s 0ₙ z) $A $x0) (η (s 0ₙ z) $A $x);
constant symbol {|!_≡___refl|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, ({|!_≡_|} A (η (s 0ₙ z) A x) (η (s 0ₙ z) A x))))));
rule η _ ({|!_≡_|} _ _ _) ({|!_≡___refl|} $A $x) ↪ {|!_≡___refl|} $A (η (s 0ₙ z) $A $x);
 

symbol trans : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ {|!z|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≡_|} A (η (s 0ₙ z) A x) (η (s 0ₙ z) A y)) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≡_|} A (η (s 0ₙ z) A y) (η (s 0ₙ z) A {|!z|})) (λ _0, ({|!_≡_|} A (η (s 0ₙ z) A x) (η (s 0ₙ z) A {|!z|}))))))))))))));
rule trans $A $x0 $y _ $x ({|!_≡___refl|} _ _) ↪ η (s 0ₙ z) ({|!_≡_|} $A (η (s 0ₙ z) $A $x0) (η (s 0ₙ z) $A $y)) $x;
 
symbol cong : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, B)) (λ f, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≡_|} A (η (s 0ₙ z) A x) (η (s 0ₙ z) A y)) (λ _0, ({|!_≡_|} B (η (s 0ₙ z) B (f (η (s 0ₙ z) A x))) (η (s 0ₙ z) B (f (η (s 0ₙ z) A y))))))))))))))));
rule cong $A $B $x _ $f ({|!_≡___refl|} _ _) ↪ η (s 0ₙ z) ({|!_≡_|} $B (η (s 0ₙ z) $B ($f (η (s 0ₙ z) $A $x))) (η (s 0ₙ z) $B ($f (η (s 0ₙ z) $A $x)))) ({|!_≡___refl|} $B (η (s 0ₙ z) $B ($f (η (s 0ₙ z) $A $x))));
 
