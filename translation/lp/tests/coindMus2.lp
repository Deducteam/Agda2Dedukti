require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Coinduction as Agda__Builtin__Coinduction;
require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
constant symbol TYPE__Stream : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol Stream : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⋄ (set (s 0ₙ z)))));
rule El _ (Stream $A) ↪ TYPE__Stream $A;
constant symbol {|!Stream___∷_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream A)) (λ xs, (Stream A)))))));
rule η _ (Stream _) ({|!Stream___∷_|} $A $x $xs) ↪ {|!Stream___∷_|} $A (η (s 0ₙ z) $A $x) $xs;
 

symbol zeros : El (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat);
symbol {|!___♯-0|} : El (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat));
rule zeros ↪ η (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) ({|!Stream___∷_|} Agda__Builtin__Nat.Nat (η (s 0ₙ z) Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat__zero) {|!___♯-0|});
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ {|!___♯-0|} ↪ η (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) zeros;
 
symbol natStream : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, (Stream Agda__Builtin__Nat.Nat)));
symbol {|!___♯-1|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ n, (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat))));
rule natStream $x ↪ η (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) ({|!Stream___∷_|} Agda__Builtin__Nat.Nat (η (s 0ₙ z) Agda__Builtin__Nat.Nat $x) ({|!___♯-1|} (η (s 0ₙ z) Agda__Builtin__Nat.Nat $x)));
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ ({|!___♯-1|} $n) ↪ η (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) (natStream (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (η (s 0ₙ z) Agda__Builtin__Nat.Nat $n))));
 
