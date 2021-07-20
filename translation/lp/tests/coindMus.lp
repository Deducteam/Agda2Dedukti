require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Coinduction as Agda__Builtin__Coinduction;
require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
constant symbol TYPE__Stream : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol Stream : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⋄ (set (s 0ₙ z)))));
rule El _ (Stream $A) ↪ TYPE__Stream $A;
constant symbol {|!Stream___∷_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream A)) (λ xs, (Stream A)))))));
rule η _ (Stream _) ({|!Stream___∷_|} $A $x $xs) ↪ {|!Stream___∷_|} $A (η (s 0ₙ z) $A $x) $xs;
 

symbol makeStream : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, (Stream Agda__Builtin__Nat.Nat)));
symbol {|!___♯-0|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ n, (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat))));
rule makeStream $x ↪ η (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) ({|!Stream___∷_|} Agda__Builtin__Nat.Nat (η (s 0ₙ z) Agda__Builtin__Nat.Nat $x) ({|!___♯-0|} (η (s 0ₙ z) Agda__Builtin__Nat.Nat $x)));
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ ({|!___♯-0|} $n) ↪ η (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) (makeStream (η (s 0ₙ z) Agda__Builtin__Nat.Nat $n));
 
symbol times2 : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ _0, (Stream Agda__Builtin__Nat.Nat)));
symbol {|!___♯-1|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ hd, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat)) (λ tl, (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat))))));
rule times2 ({|!Stream___∷_|} _ $x $xs) ↪ η (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) ({|!Stream___∷_|} Agda__Builtin__Nat.Nat (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.{|!_+_|} (η (s 0ₙ z) Agda__Builtin__Nat.Nat $x) (η (s 0ₙ z) Agda__Builtin__Nat.Nat $x))) ({|!___♯-1|} (η (s 0ₙ z) Agda__Builtin__Nat.Nat $x) $xs));
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ ({|!___♯-1|} $hd $tl) ↪ η (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) (times2 (η (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) $tl)));
 
symbol nth : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ _0, Agda__Builtin__Nat.Nat))));
rule nth Agda__Builtin__Nat.Nat__zero ({|!Stream___∷_|} _ $x $xs) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat $x;
rule nth (Agda__Builtin__Nat.Nat__suc $x0) ({|!Stream___∷_|} _ $x $xs) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (nth (η (s 0ₙ z) Agda__Builtin__Nat.Nat $x0) (η (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) $xs)));
 
symbol zeros : El (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat);
symbol {|!♯-2|} : El (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat));

rule Agda__Builtin__Coinduction.{|!♭|} _ _ {|!♯-2|} ↪ η (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) zeros;
 
constant symbol TYPE__SP : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π B : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol SP : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ B, (⋄ (set (s 0ₙ z)))))));
rule El _ (SP $A $B) ↪ TYPE__SP $A $B;
constant symbol SP__get : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, (SP A B))) (λ f, (SP A B)))))));
constant symbol SP__put : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) B (λ b, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (SP A B)) (λ sp, (SP A B)))))))));
rule η _ (SP _ _) (SP__get $A $B $f) ↪ SP__get $A $B (λ _0, η (s 0ₙ z) (SP $A $B) ($f (η (s 0ₙ z) $A _0)));
rule η _ (SP _ _) (SP__put $A $B $b $sp) ↪ SP__put $A $B (η (s 0ₙ z) $B $b) $sp;
 


symbol eat : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (SP A B) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ _0, (Stream B)))))))));
symbol {|!___♯-3|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) B (λ b, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (SP A B)) (λ sp, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ {|!as|}, (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream B))))))))))));
rule eat $A $B (SP__get _ _ $f) ({|!Stream___∷_|} _ $x $xs) ↪ η (s 0ₙ z) (Stream $B) (eat $A $B (η (s 0ₙ z) (SP $A $B) ($f (η (s 0ₙ z) $A $x))) (η (s 0ₙ z) (Stream $A) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream $A) $xs)));
rule eat $A $B (SP__put _ _ $b $sp) $x ↪ η (s 0ₙ z) (Stream $B) ({|!Stream___∷_|} $B (η (s 0ₙ z) $B $b) ({|!___♯-3|} $A $B (η (s 0ₙ z) $B $b) $sp (η (s 0ₙ z) (Stream $A) $x)));
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ ({|!___♯-3|} $A $B $b $sp ${|!as|}) ↪ η (s 0ₙ z) (Stream $B) (eat $A $B (η (s 0ₙ z) (SP $A $B) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (SP $A $B) $sp)) (η (s 0ₙ z) (Stream $A) ${|!as|}));
 
symbol {|!_∘_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ C, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (SP B C) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (SP A B) (λ _0, (SP A C)))))))))));
symbol {|!___♯-4|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ C, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) C (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (SP B C)) (λ {|!sp₁|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (SP A B) (λ {|!sp₂|}, (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (SP A C))))))))))))));
rule {|!_∘_|} $A $B $C (SP__get _ _ $f0) (SP__get _ _ $f) ↪ η (s 0ₙ z) (SP $A $C) (SP__get $A $C (λ x, η (s 0ₙ z) (SP $A $C) ({|!_∘_|} $A $B $C (η (s 0ₙ z) (SP $B $C) (SP__get $B $C (λ _0, η (s 0ₙ z) (SP $B $C) ($f0 (η (s 0ₙ z) $B _0))))) (η (s 0ₙ z) (SP $A $B) ($f (η (s 0ₙ z) $A x))))));
rule {|!_∘_|} $A $B $C (SP__get _ _ $f) (SP__put _ _ $b $sp) ↪ η (s 0ₙ z) (SP $A $C) ({|!_∘_|} $A $B $C (η (s 0ₙ z) (SP $B $C) ($f (η (s 0ₙ z) $B $b))) (η (s 0ₙ z) (SP $A $B) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (SP $A $B) $sp)));
rule {|!_∘_|} $A $B $C (SP__put _ _ $b $sp) $x ↪ η (s 0ₙ z) (SP $A $C) (SP__put $A $C (η (s 0ₙ z) $C $b) ({|!___♯-4|} $A $B $C (η (s 0ₙ z) $C $b) $sp (η (s 0ₙ z) (SP $A $B) $x)));
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ ({|!___♯-4|} $A $B $C $x ${|!sp₁|} ${|!sp₂|}) ↪ η (s 0ₙ z) (SP $A $C) ({|!_∘_|} $A $B $C (η (s 0ₙ z) (SP $B $C) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (SP $B $C) ${|!sp₁|})) (η (s 0ₙ z) (SP $A $B) ${|!sp₂|}));
 
