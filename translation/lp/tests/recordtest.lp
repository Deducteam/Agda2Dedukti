require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
constant symbol TYPE__Pair : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π B : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol Pair : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ B, (⋄ (set (s 0ₙ z)))))));
rule El _ (Pair $A $B) ↪ TYPE__Pair $A $B;
constant symbol {|!Pair'constructor|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ fst, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) B (λ snd, (Pair A B)))))))));
symbol Pair__fst : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Pair A B) (λ r, A))))));
symbol Pair__snd : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Pair A B) (λ r, B))))));

rule η _ (Pair $A $B) $y ↪ {|!Pair'constructor|} $A $B (η (s 0ₙ z) $A (Pair__fst $A $B $y)) (η (s 0ₙ z) $B (Pair__snd $A $B $y));
 
rule Pair__fst $A $B ({|!Pair'constructor|} _ _ $fst $snd) ↪ η (s 0ₙ z) $A $fst;
 
rule Pair__snd $A $B ({|!Pair'constructor|} _ _ $fst $snd) ↪ η (s 0ₙ z) $B $snd;
 
symbol p23 : El (set (s 0ₙ z)) (Pair Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat);
rule p23 ↪ η (s 0ₙ z) (Pair Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat) ({|!Pair'constructor|} Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero))) (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)))));
 
symbol p34 : El (set (s 0ₙ z)) (Pair Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat);
rule Pair__fst _ _ p34 ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)));
rule Pair__snd _ _ p34 ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero))));
 
symbol p56 : El (set (s 0ₙ z)) (Pair Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat);
rule Pair__fst _ _ p56 ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)))));
rule Pair__snd _ _ p56 ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero))))));
 
symbol p78 : El (set (s 0ₙ z)) (Pair Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat);
symbol {|!'extendedlambda0|} : El (set (s 0ₙ z)) (Pair Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat);
rule p78 ↪ η (s 0ₙ z) (Pair Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat) {|!'extendedlambda0|};
 
rule Pair__fst _ _ {|!'extendedlambda0|} ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)))))));
rule Pair__snd _ _ {|!'extendedlambda0|} ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero))))))));
 
constant symbol TYPE__Pair2 : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π B : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol Pair2 : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ B, (⋄ (set (s 0ₙ z)))))));
rule El _ (Pair2 $A $B) ↪ TYPE__Pair2 $A $B;
symbol Pair2__fst : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Pair2 A B) (λ r, A))))));
symbol Pair2__snd : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Pair2 A B) (λ r, B))))));
constant symbol {|!_,_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ fst, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) B (λ snd, (Pair2 A B)))))))));
rule η _ (Pair2 $A $B) $y ↪ {|!_,_|} $A $B (η (s 0ₙ z) $A (Pair2__fst $A $B $y)) (η (s 0ₙ z) $B (Pair2__snd $A $B $y));
 
rule Pair2__fst $A $B ({|!_,_|} _ _ $fst $snd) ↪ η (s 0ₙ z) $A $fst;
 
rule Pair2__snd $A $B ({|!_,_|} _ _ $fst $snd) ↪ η (s 0ₙ z) $B $snd;
 

symbol p45 : El (set (s 0ₙ z)) (Pair2 Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat);
rule p45 ↪ η (s 0ₙ z) (Pair2 Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat) ({|!_,_|} Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero))))) (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)))))));
 
