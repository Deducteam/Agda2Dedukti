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
rule b1 ↪ η (s 0ₙ z) Box (cons (η (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc (Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero)))));
 
symbol b2 : El (set (s 0ₙ z)) Box;

symbol p : El (set (s 0ₙ z)) ({|!_≡_|} Box (η (s 0ₙ z) Box b1) (η (s 0ₙ z) Box b2));
rule p ↪ η (s 0ₙ z) ({|!_≡_|} Box (η (s 0ₙ z) Box b1) (η (s 0ₙ z) Box b2)) ({|!_≡___refl|} Box (η (s 0ₙ z) Box b1));
 
constant symbol {|!TYPE__Box'|} : TYPE;
constant symbol {|!Box'|} : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ {|!Box'|} ↪ {|!TYPE__Box'|};
symbol {|!Box'__openBox'|} : El (set (s 0ₙ z)) (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) {|!Box'|} (λ r, Agda__Builtin__Nat.Nat));
constant symbol {|!cons'|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ {|!openBox'|}, {|!Box'|}));
rule η _ {|!Box'|} $y ↪ $y;
 
rule {|!Box'__openBox'|} ({|!cons'|} ${|!openBox'|}) ↪ η (s 0ₙ z) Agda__Builtin__Nat.Nat ${|!openBox'|};
 

symbol {|!b1'|} : El (set (s 0ₙ z)) {|!Box'|};

symbol {|!b2'|} : El (set (s 0ₙ z)) {|!Box'|};

symbol {|!p'|} : El (set (s 0ₙ z)) ({|!_≡_|} {|!Box'|} {|!b1'|} {|!b2'|});
rule {|!p'|} ↪ η (s 0ₙ z) ({|!_≡_|} {|!Box'|} {|!b1'|} {|!b2'|}) ({|!_≡___refl|} {|!Box'|} {|!b1'|});
 
constant symbol TYPE__Unit : TYPE;
constant symbol Unit : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ Unit ↪ TYPE__Unit;
constant symbol {|!Unit'constructor|} : El (set (s 0ₙ z)) Unit;
rule η _ Unit $y ↪ {|!Unit'constructor|};
 

symbol pro : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Unit (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Unit (λ y, ({|!_≡_|} Unit (η (s 0ₙ z) Unit x) (η (s 0ₙ z) Unit y))))));
rule pro $x $y ↪ η (s 0ₙ z) ({|!_≡_|} Unit (η (s 0ₙ z) Unit $x) (η (s 0ₙ z) Unit $y)) ({|!_≡___refl|} Unit (η (s 0ₙ z) Unit {|!Unit'constructor|}));
 
