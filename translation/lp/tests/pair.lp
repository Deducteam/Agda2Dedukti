require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

constant symbol TYPE__X : TYPE;
constant symbol X : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ X ↪ TYPE__X;
constant symbol X__arr : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) X (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) X (λ _0, X))));


constant symbol TYPE__and : Π _0 : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π _0 : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol and : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ _0, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ _0, (⋄ (set (s 0ₙ z)))))));
rule El _ (and $x0 $x) ↪ TYPE__and $x0 $x;
constant symbol and__pair : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (and A B)))));


symbol subtype : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) X (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) X (λ _0, (⋄ (set (s 0ₙ z)))))));
rule subtype (X__arr $x2 $x1) (X__arr $x0 $x) ↪ and (subtype $x0 $x2) (subtype $x1 $x);
 
