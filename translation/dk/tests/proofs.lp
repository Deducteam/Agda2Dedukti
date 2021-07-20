require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Equality as Agda__Builtin__Equality;
require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
symbol trans : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ {|!z|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) A x y) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) A y {|!z|}) (λ _0, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) A x {|!z|})))))))))))));
rule trans $A $x0 $y _ $x (Agda__Builtin__Equality.{|!_≡___refl|} _ _ _) ↪ $x;
 
symbol cong : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, B)) (λ f, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) A x y) (λ _0, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) B (f x) (f y))))))))))))));
rule cong $A $B $x _ $f (Agda__Builtin__Equality.{|!_≡___refl|} _ _ _) ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) $B ($f $x);
 
symbol {|!+-assoc|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ {|!z|}, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.{|!_+_|} (Agda__Builtin__Nat.{|!_+_|} x y) {|!z|}) (Agda__Builtin__Nat.{|!_+_|} x (Agda__Builtin__Nat.{|!_+_|} y {|!z|})))))))));
rule {|!+-assoc|} Agda__Builtin__Nat.Nat__zero $y ${|!z|} ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.{|!_+_|} (Agda__Builtin__Nat.{|!_+_|} Agda__Builtin__Nat.Nat__zero $y) ${|!z|});
rule {|!+-assoc|} (Agda__Builtin__Nat.Nat__suc $x) $y ${|!z|} ↪ cong Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.{|!_+_|} (Agda__Builtin__Nat.{|!_+_|} $x $y) ${|!z|}) (Agda__Builtin__Nat.{|!_+_|} $x (Agda__Builtin__Nat.{|!_+_|} $y ${|!z|})) Agda__Builtin__Nat.Nat__suc ({|!+-assoc|} $x $y ${|!z|});
 
