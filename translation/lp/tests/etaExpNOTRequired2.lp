require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Equality as Agda__Builtin__Equality;
require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
constant symbol TYPE__R : TYPE;
constant symbol R : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ R ↪ TYPE__R;
symbol R__n : El (set (s 0ₙ z)) (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) R (λ r, Agda__Builtin__Nat.Nat));
constant symbol cons : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ n, R));
rule η _ R $y ↪ cons (η (s 0ₙ z) Agda__Builtin__Nat.Nat (R__n $y));
 
rule R__n (cons $n) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat $n;
 

symbol bla : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) R (λ x, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) R (η (s 0ₙ ((s 0ₙ z) ⊕ z)) R x) (η (s 0ₙ ((s 0ₙ z) ⊕ z)) R x))));
rule bla $x ↪ η (s 0ₙ z) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) R (η (s 0ₙ ((s 0ₙ z) ⊕ z)) R $x) (η (s 0ₙ ((s 0ₙ z) ⊕ z)) R $x)) (Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) R (η (s 0ₙ ((s 0ₙ z) ⊕ z)) R $x));
 
symbol bla2 : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, A)) (λ x, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, A)) (λ _0, η (s 0ₙ z) A (x (η (s 0ₙ z) A _0))) (λ _0, η (s 0ₙ z) A (x (η (s 0ₙ z) A _0))))))));
rule bla2 $A $x ↪ η (s 0ₙ z) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) $A (λ _0, $A)) (λ _0, η (s 0ₙ z) $A ($x (η (s 0ₙ z) $A _0))) (λ _0, η (s 0ₙ z) $A ($x (η (s 0ₙ z) $A _0)))) (Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) $A (λ _0, $A)) (λ _0, η (s 0ₙ z) $A ($x (η (s 0ₙ z) $A _0))));
 
