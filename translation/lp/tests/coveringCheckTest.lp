require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
symbol tr : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, Agda__Builtin__Nat.Nat));
rule tr Agda__Builtin__Nat.Nat__zero ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat__zero;
rule tr (Agda__Builtin__Nat.Nat__suc $x) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat__zero;
 
symbol trr : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, Agda__Builtin__Nat.Nat))));
rule trr Agda__Builtin__Nat.Nat__zero Agda__Builtin__Nat.Nat__zero ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero));
rule trr Agda__Builtin__Nat.Nat__zero (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero));
rule trr Agda__Builtin__Nat.Nat__zero (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero));
rule trr Agda__Builtin__Nat.Nat__zero (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero))) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero);
rule trr Agda__Builtin__Nat.Nat__zero (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc $x)))) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero));
rule trr (Agda__Builtin__Nat.Nat__suc $x0) $x ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)));
 
