require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
symbol f : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, Agda__Builtin__Nat.Nat));
symbol g : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, Agda__Builtin__Nat.Nat));
rule f $x ↪ g $x;
 
rule g Agda__Builtin__Nat.Nat__zero ↪ Agda__Builtin__Nat.Nat__zero;
rule g (Agda__Builtin__Nat.Nat__suc $x) ↪ f $x;
 
