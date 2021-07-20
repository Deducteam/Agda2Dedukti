require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
constant symbol TYPE__Pair : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol Pair : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⋄ (set (s 0ₙ z)))));
rule El _ (Pair $A) ↪ TYPE__Pair $A;
constant symbol {|!Pair'constructor|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, A)) (λ n1, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ n2, (Pair A)))))));
symbol Pair__n1 : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Pair A) (λ r, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, A))))));
symbol Pair__n2 : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Pair A) (λ r, A))));

rule η _ (Pair $A) $y ↪ {|!Pair'constructor|} $A (λ _0 : El (set (s 0ₙ z)) Agda__Builtin__Nat.Nat, η (s 0ₙ z) $A (Pair__n1 $A $y (η (s 0ₙ z) Agda__Builtin__Nat.Nat _0))) (η (s 0ₙ z) $A (Pair__n2 $A $y));
 
rule Pair__n1 $A ({|!Pair'constructor|} _ $n1 $n2) ↪ λ _0, η (s 0ₙ z) $A ($n1 (η (s 0ₙ z) Agda__Builtin__Nat.Nat _0));
 
rule Pair__n2 $A ({|!Pair'constructor|} _ $n1 $n2) ↪ η (s 0ₙ z) $A $n2;
 
symbol el : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, (Pair Agda__Builtin__Nat.Nat)))));
rule Pair__n1 _ (el $x1 $x0) $x ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.{|!_+_|} (η (s 0ₙ z) Agda__Builtin__Nat.Nat $x1) (η (s 0ₙ z) Agda__Builtin__Nat.Nat $x));
rule Pair__n2 _ (el $x0 $x) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat $x;
 
