require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
constant symbol TYPE__Box : TYPE;
constant symbol Box : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ Box ↪ TYPE__Box;
symbol Box__openBox : El (set (s 0ₙ z)) (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) Box (λ r, Agda__Builtin__Nat.Nat));
constant symbol cons : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ openBox, Box));
rule η _ Box $y ↪ cons (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Box__openBox $y));
 
rule Box__openBox (cons $openBox) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat $openBox;
 

symbol b1 : El (set (s 0ₙ z)) Box;
rule b1 ↪ η (s 0ₙ z) Box (cons (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)))));
 
symbol b2 : El (set (s 0ₙ z)) Box;

