require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
constant symbol {|!TYPE___≡_|} : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π _0 : El (set (s 0ₙ z)) A, Π _0 : El (set (s 0ₙ z)) A, TYPE;
constant symbol {|!_≡_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z)))))))));
rule El _ ({|!_≡_|} $A $x0 $x) ↪ {|!TYPE___≡_|} $A (η (s 0ₙ z) $A $x0) (η (s 0ₙ z) $A $x);
constant symbol {|!_≡___refl|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, ({|!_≡_|} A (η (s 0ₙ z) A a) (η (s 0ₙ z) A a))))));
rule η _ ({|!_≡_|} _ _ _) ({|!_≡___refl|} $A $a) ↪ {|!_≡___refl|} $A (η (s 0ₙ z) $A $a);
 

constant symbol TYPE__Box : TYPE;
constant symbol Box : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ Box ↪ TYPE__Box;
symbol Box__openBox : El (set (s 0ₙ z)) (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) Box (λ r, Agda__Builtin__Nat.Nat));
constant symbol cons : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ openBox, Box));
rule η _ Box $y ↪ cons (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Box__openBox $y));
 
rule Box__openBox (cons $openBox) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat $openBox;
 

symbol b1 : El (set (s 0ₙ z)) Box;
rule Box__openBox b1 ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)));
 
symbol b2 : El (set (s 0ₙ z)) Box;
rule b2 ↪ η (s 0ₙ z) Box (cons (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)))));
 
symbol {|!b2'|} : El (set (s 0ₙ z)) Box;
rule {|!b2'|} ↪ η (s 0ₙ z) Box (cons (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)))));
 
symbol b3 : El (set (s 0ₙ z)) Box;
rule Box__openBox b3 ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)));
 
symbol b4 : El (set (s 0ₙ z)) Box;
symbol {|!'extendedlambda0|} : El (set (s 0ₙ z)) Box;
rule b4 ↪ η (s 0ₙ z) Box {|!'extendedlambda0|};
 
rule Box__openBox {|!'extendedlambda0|} ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)));
 
symbol b5 : El (set (s 0ₙ z)) Box;
symbol {|!'extendedlambda1|} : El (set (s 0ₙ z)) Box;
rule b5 ↪ η (s 0ₙ z) Box {|!'extendedlambda1|};
 
rule Box__openBox {|!'extendedlambda1|} ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)));
 
symbol p : El (set (s 0ₙ z)) ({|!_≡_|} Box (η (s 0ₙ z) Box b1) (η (s 0ₙ z) Box b2));
rule p ↪ η (s 0ₙ z) ({|!_≡_|} Box (η (s 0ₙ z) Box b1) (η (s 0ₙ z) Box b2)) ({|!_≡___refl|} Box (η (s 0ₙ z) Box b1));
 
symbol {|!p'|} : El (set (s 0ₙ z)) ({|!_≡_|} Box (η (s 0ₙ z) Box {|!b2'|}) (η (s 0ₙ z) Box b2));
rule {|!p'|} ↪ η (s 0ₙ z) ({|!_≡_|} Box (η (s 0ₙ z) Box {|!b2'|}) (η (s 0ₙ z) Box b2)) ({|!_≡___refl|} Box (η (s 0ₙ z) Box {|!b2'|}));
 
symbol p2 : El (set (s 0ₙ z)) ({|!_≡_|} Box (η (s 0ₙ z) Box b3) (η (s 0ₙ z) Box b1));
rule p2 ↪ η (s 0ₙ z) ({|!_≡_|} Box (η (s 0ₙ z) Box b3) (η (s 0ₙ z) Box b1)) ({|!_≡___refl|} Box (η (s 0ₙ z) Box b3));
 
symbol p3 : El (set (s 0ₙ z)) ({|!_≡_|} Box (η (s 0ₙ z) Box b1) (η (s 0ₙ z) Box b5));
rule p3 ↪ η (s 0ₙ z) ({|!_≡_|} Box (η (s 0ₙ z) Box b1) (η (s 0ₙ z) Box b5)) ({|!_≡___refl|} Box (η (s 0ₙ z) Box b1));
 
symbol p4 : El (set (s 0ₙ z)) ({|!_≡_|} Box (η (s 0ₙ z) Box b4) (η (s 0ₙ z) Box b5));
rule p4 ↪ η (s 0ₙ z) ({|!_≡_|} Box (η (s 0ₙ z) Box b4) (η (s 0ₙ z) Box b5)) ({|!_≡___refl|} Box (η (s 0ₙ z) Box b4));
 
constant symbol TYPE__Nat2 : TYPE;
constant symbol Nat2 : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ Nat2 ↪ TYPE__Nat2;
symbol Nat2__a : El (set (s 0ₙ z)) (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) Nat2 (λ r, Agda__Builtin__Nat.Nat));
symbol Nat2__b : El (set (s 0ₙ z)) (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) Nat2 (λ r, Agda__Builtin__Nat.Nat));
constant symbol {|!Nat2'constructor|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ b, Nat2))));
rule η _ Nat2 $y ↪ {|!Nat2'constructor|} (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Nat2__a $y)) (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Nat2__b $y));
 
rule Nat2__a ({|!Nat2'constructor|} $a $b) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat $a;
 
rule Nat2__b ({|!Nat2'constructor|} $a $b) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat $b;
 

