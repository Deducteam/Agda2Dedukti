require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
symbol max : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, Agda__Builtin__Nat.Nat))));
rule max Agda__Builtin__Nat.Nat__zero Agda__Builtin__Nat.Nat__zero ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat__zero;
rule max Agda__Builtin__Nat.Nat__zero (Agda__Builtin__Nat.Nat__suc $x) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (η (s 0ₙ z) Agda__Builtin__Nat.Nat $x));
rule max (Agda__Builtin__Nat.Nat__suc $x) Agda__Builtin__Nat.Nat__zero ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (η (s 0ₙ z) Agda__Builtin__Nat.Nat $x));
rule max (Agda__Builtin__Nat.Nat__suc $x0) (Agda__Builtin__Nat.Nat__suc $x) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (η (s 0ₙ z) Agda__Builtin__Nat.Nat (max (η (s 0ₙ z) Agda__Builtin__Nat.Nat $x0) (η (s 0ₙ z) Agda__Builtin__Nat.Nat $x))));
 
