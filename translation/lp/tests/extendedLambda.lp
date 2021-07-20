require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
constant symbol TYPE__Pair : TYPE;
constant symbol Pair : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ Pair ↪ TYPE__Pair;
constant symbol {|!Pair'constructor|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ fst, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ snd, Pair))));
symbol Pair__fst : El (set (s 0ₙ z)) (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) Pair (λ r, Agda__Builtin__Nat.Nat));
symbol Pair__snd : El (set (s 0ₙ z)) (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) Pair (λ r, Agda__Builtin__Nat.Nat));

rule η _ Pair $y ↪ {|!Pair'constructor|} (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Pair__fst $y)) (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Pair__snd $y));
 
rule Pair__fst ({|!Pair'constructor|} $fst $snd) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat $fst;
 
rule Pair__snd ({|!Pair'constructor|} $fst $snd) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat $snd;
 
symbol bla : El (set (s 0ₙ z)) Pair;
symbol {|!'extendedlambda0|} : El (set (s 0ₙ z)) Pair;
rule bla ↪ η (s 0ₙ z) Pair {|!'extendedlambda0|};
 
rule Pair__fst {|!'extendedlambda0|} ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero))));
rule Pair__snd {|!'extendedlambda0|} ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero));
 
symbol bla2 : El (set (s 0ₙ z)) Pair;
symbol {|!'extendedlambda1|} : El (set (s 0ₙ z)) Pair;
rule bla2 ↪ η (s 0ₙ z) Pair {|!'extendedlambda1|};
 
rule Pair__fst {|!'extendedlambda1|} ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero);
rule Pair__snd {|!'extendedlambda1|} ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat__zero;
 
