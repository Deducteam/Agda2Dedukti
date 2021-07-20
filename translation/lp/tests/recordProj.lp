require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Equality as Agda__Builtin__Equality;
require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
constant symbol TYPE__Rec : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π B : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol Rec : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ B, (⋄ (set (s 0ₙ z)))))));
rule El _ (Rec $A $B) ↪ TYPE__Rec $A $B;
symbol Rec__a : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Rec A B) (λ r, A))))));
symbol Rec__b : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Rec A B) (λ r, B))))));
constant symbol cons : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) B (λ b, (Rec A B)))))))));
rule η _ (Rec $A $B) $y ↪ cons $A $B (η (s 0ₙ z) $A (Rec__a $A $B $y)) (η (s 0ₙ z) $B (Rec__b $A $B $y));
 
rule Rec__a $A $B (cons _ _ $a $b) ↪ η (s 0ₙ z) $A $a;
 
rule Rec__b $A $B (cons _ _ $a $b) ↪ η (s 0ₙ z) $B $b;
 

symbol rec : El (set (s 0ₙ z)) (Rec Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat);
rule rec ↪ η (s 0ₙ z) (Rec Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat) (cons Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)))) (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)))))));
 
symbol equality : El (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Nat.Nat (η (s 0ₙ ((s 0ₙ z) ⊕ z)) Agda__Builtin__Nat.Nat (Rec__a Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat rec)) (η (s 0ₙ ((s 0ₙ z) ⊕ z)) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)))));
rule equality ↪ η (s 0ₙ z) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Nat.Nat (η (s 0ₙ ((s 0ₙ z) ⊕ z)) Agda__Builtin__Nat.Nat (Rec__a Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat rec)) (η (s 0ₙ ((s 0ₙ z) ⊕ z)) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero))))) (Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Nat.Nat (η (s 0ₙ ((s 0ₙ z) ⊕ z)) Agda__Builtin__Nat.Nat (Rec__a Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat rec)));
 
