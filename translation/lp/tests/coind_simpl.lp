require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
constant symbol TYPE__Stream : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol Stream : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⋄ (set (s 0ₙ z)))));
rule El _ (Stream $A) ↪ TYPE__Stream $A;
constant symbol {|!Stream'constructor|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ hd, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ tl, (Stream A)))))));
symbol Stream__hd : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ r, A))));
symbol Stream__tl : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ r, (Stream A)))));

rule η _ (Stream $A) $y ↪ $y;
 
rule Stream__hd $A ({|!Stream'constructor|} _ $hd $tl) ↪ η (s 0ₙ z) $A $hd;
 
rule Stream__tl $A ({|!Stream'constructor|} _ $hd $tl) ↪ $tl;
 
symbol zeros : El (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat);
rule Stream__hd _ zeros ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat__zero;
rule Stream__tl _ zeros ↪ zeros;
 
