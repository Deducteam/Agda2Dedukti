require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

constant symbol TYPE__X : TYPE;
constant symbol X : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ X ↪ TYPE__X;
constant symbol X__arr : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) X (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) X (λ _0, X))));
rule η _ X (X__arr $x0 $x) ↪ X__arr (η (s 0ₙ z) X $x0) (η (s 0ₙ z) X $x);
 

constant symbol TYPE__and : Π _0 : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π _0 : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol and : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ _0, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ _0, (⋄ (set (s 0ₙ z)))))));
rule El _ (and $x0 $x) ↪ TYPE__and $x0 $x;
constant symbol and__pair : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (and A B)))));
rule η _ (and _ _) (and__pair $A $B) ↪ and__pair $A $B;
 

symbol subtype : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) X (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) X (λ _0, (⋄ (set (s 0ₙ z)))))));
rule subtype (X__arr $x2 $x1) (X__arr $x0 $x) ↪ and (subtype (η (s 0ₙ z) X $x0) (η (s 0ₙ z) X $x2)) (subtype (η (s 0ₙ z) X $x1) (η (s 0ₙ z) X $x));
 
