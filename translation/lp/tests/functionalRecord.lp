require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
constant symbol TYPE__r : TYPE;
constant symbol r : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ r ↪ TYPE__r;
symbol r__n : El (set (s 0ₙ z)) (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) r (λ r, Agda__Builtin__Nat.Nat));
symbol r__m : El (set (s 0ₙ z)) (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) r (λ r, Agda__Builtin__Nat.Nat));
constant symbol cons : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ n, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ m, r))));
rule η _ r $y ↪ cons (η (s 0ₙ z) Agda__Builtin__Nat.Nat (r__n $y)) (η (s 0ₙ z) Agda__Builtin__Nat.Nat (r__m $y));
 
rule r__n (cons $n $m) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat $n;
 
rule r__m (cons $n $m) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat $m;
 

constant symbol TYPE__rr : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol rr : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⋄ (set (s 0ₙ z)))));
rule El _ (rr $A) ↪ TYPE__rr $A;
symbol rr__nn : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (rr A) (λ r, A))));
symbol rr__mm : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (rr A) (λ r, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, Agda__Builtin__Nat.Nat))))));
constant symbol conss : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ nn, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, Agda__Builtin__Nat.Nat)) (λ mm, (rr A)))))));
rule η _ (rr $A) $y ↪ conss $A (η (s 0ₙ z) $A (rr__nn $A $y)) (λ _0 : El (set (s 0ₙ z)) $A, η (s 0ₙ z) Agda__Builtin__Nat.Nat (rr__mm $A $y (η (s 0ₙ z) $A _0)));
 
rule rr__nn $A (conss _ $nn $mm) ↪ η (s 0ₙ z) $A $nn;
 
rule rr__mm $A (conss _ $nn $mm) ↪ λ _0, η (s 0ₙ z) Agda__Builtin__Nat.Nat ($mm (η (s 0ₙ z) $A _0));
 

