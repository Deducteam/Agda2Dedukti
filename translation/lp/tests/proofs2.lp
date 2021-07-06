require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
constant symbol {|!TYPE___≡_|} : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π _0 : El (set (s 0ₙ z)) A, Π _0 : El (set (s 0ₙ z)) A, TYPE;
constant symbol {|!_≡_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z)))))))));
rule El _ ({|!_≡_|} $A $x0 $x) ↪ {|!TYPE___≡_|} $A $x0 $x;
constant symbol {|!_≡___refl|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, ({|!_≡_|} A a a)))));


symbol trans : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ {|!z|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≡_|} A x y) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≡_|} A y {|!z|}) (λ _0, ({|!_≡_|} A x {|!z|})))))))))))));
rule trans $A $x0 $y _ $x ({|!_≡___refl|} _ _) ↪ $x;
 
symbol cong : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, B)) (λ f, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≡_|} A x y) (λ _0, ({|!_≡_|} B (f x) (f y))))))))))))));
rule cong $A $B $x _ $f ({|!_≡___refl|} _ _) ↪ {|!_≡___refl|} $B ($f $x);
 
symbol {|!+-assoc|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ {|!z|}, ({|!_≡_|} Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.{|!_+_|} (Agda__Builtin__Nat.{|!_+_|} x y) {|!z|}) (Agda__Builtin__Nat.{|!_+_|} x (Agda__Builtin__Nat.{|!_+_|} y {|!z|})))))))));
rule {|!+-assoc|} Agda__Builtin__Nat.Nat__zero $y ${|!z|} ↪ {|!_≡___refl|} Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.{|!_+_|} (Agda__Builtin__Nat.{|!_+_|} Agda__Builtin__Nat.Nat__zero $y) ${|!z|});
rule {|!+-assoc|} (Agda__Builtin__Nat.Nat__suc $x) $y ${|!z|} ↪ cong Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.{|!_+_|} (Agda__Builtin__Nat.{|!_+_|} $x $y) ${|!z|}) (Agda__Builtin__Nat.{|!_+_|} $x (Agda__Builtin__Nat.{|!_+_|} $y ${|!z|})) Agda__Builtin__Nat.Nat__suc ({|!+-assoc|} $x $y ${|!z|});
 
