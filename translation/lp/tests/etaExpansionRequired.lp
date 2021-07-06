require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Equality as Agda__Builtin__Equality;
require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
require tests.Agda__Primitive as Agda__Primitive;
constant symbol a : El (set (s 0ₙ z)) Agda__Primitive.Level;

constant symbol A : El setω (∀ (λ a, set (s (sₙ 0ₙ) (a ⊕ z))) (λ a, ⋄ (set (s 0ₙ (a ⊕ z)))));

constant symbol TYPE__R : Π a : L, Π A : El (set (s (sₙ 0ₙ) (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))), TYPE;
constant symbol R : El setω (∀ (λ a, set (s (sₙ (sₙ 0ₙ)) (a ⊕ z))) (λ a, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set (s (sₙ (sₙ 0ₙ)) (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⋄ (set (s (sₙ 0ₙ) (a ⊕ z)))))));
rule El _ (R $a $A) ↪ TYPE__R $a $A;
symbol R__n : El setω (∀ (λ a, set (s (sₙ 0ₙ) (a ⊕ z))) (λ a, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set (s (sₙ 0ₙ) (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⇝proj (set (s (sₙ 0ₙ) (a ⊕ z))) (set (s 0ₙ z)) (R a A) (λ r, Agda__Builtin__Nat.Nat)))));
symbol R__m : El setω (∀ (λ a, set (s (sₙ 0ₙ) (a ⊕ z))) (λ a, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set (s (sₙ 0ₙ) (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⇝proj (set (s (sₙ 0ₙ) (a ⊕ z))) (set (s 0ₙ (a ⊕ z))) (R a A) (λ r, A)))));
constant symbol cons : El setω (∀ (λ a, set (s (sₙ 0ₙ) (a ⊕ z))) (λ a, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set (s (sₙ 0ₙ) (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) (a ⊕ z))) Agda__Builtin__Nat.Nat (λ n, (⇝ (set (s 0ₙ (a ⊕ z))) (set (s (sₙ 0ₙ) (a ⊕ z))) A (λ m, (R a A))))))));

rule R__n $a $A (cons _ _ $n $m) ↪ $n;
 
rule R__m $a $A (cons _ _ $n $m) ↪ $m;
 

symbol f : El setω (∀ (λ {|!A'a|}, set (s (sₙ 0ₙ) ({|!A'a|} ⊕ z))) (λ {|!A'a|}, ⇝ (set (s (sₙ 0ₙ) ({|!A'a|} ⊕ z))) (set (s (sₙ 0ₙ) ({|!A'a|} ⊕ z))) (⋄ (set (s 0ₙ ({|!A'a|} ⊕ z)))) (λ A, (⇝ (set (s (sₙ 0ₙ) ({|!A'a|} ⊕ z))) (set (s (sₙ 0ₙ) z)) (R {|!A'a|} A) (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) Agda__Builtin__Nat.Nat (λ _0, (R (s 0ₙ z) Agda__Builtin__Nat.Nat))))))));
rule f ${|!A'a|} $A (cons _ _ $n $m) $x ↪ cons (s 0ₙ z) Agda__Builtin__Nat.Nat $x $n;
 
symbol bla : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (R (s 0ₙ z) Agda__Builtin__Nat.Nat) (λ x, (Agda__Builtin__Equality.{|!_≡_|} (s (sₙ 0ₙ) z) (R (s 0ₙ z) Agda__Builtin__Nat.Nat) x x)));
rule bla $x ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s (sₙ 0ₙ) z) (R (s 0ₙ z) Agda__Builtin__Nat.Nat) $x;
 
symbol bla2 : El setω (∀ (λ {|!A'a|}, set (s (sₙ 0ₙ) ({|!A'a|} ⊕ z))) (λ {|!A'a|}, ⇝ (set (s (sₙ 0ₙ) ({|!A'a|} ⊕ z))) (set (s 0ₙ ({|!A'a|} ⊕ z))) (⋄ (set (s 0ₙ ({|!A'a|} ⊕ z)))) (λ A, (⇝ (set (s 0ₙ ({|!A'a|} ⊕ z))) (set (s 0ₙ ({|!A'a|} ⊕ z))) (⇝ (set (s 0ₙ ({|!A'a|} ⊕ z))) (set (s 0ₙ ({|!A'a|} ⊕ z))) A (λ _0, A)) (λ x, (Agda__Builtin__Equality.{|!_≡_|} {|!A'a|} (⇝ (set (s 0ₙ ({|!A'a|} ⊕ z))) (set (s 0ₙ ({|!A'a|} ⊕ z))) A (λ _0, A)) x x))))));
rule bla2 ${|!A'a|} $A $x ↪ Agda__Builtin__Equality.{|!_≡___refl|} ${|!A'a|} (⇝ (set (s 0ₙ (${|!A'a|} ⊕ z))) (set (s 0ₙ (${|!A'a|} ⊕ z))) $A (λ _0, $A)) $x;
 
