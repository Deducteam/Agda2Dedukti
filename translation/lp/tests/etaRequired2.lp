require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

constant symbol {|!TYPE___≡_|} : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π _0 : El (set (s 0ₙ z)) A, Π _0 : El (set (s 0ₙ z)) A, TYPE;
constant symbol {|!_≡_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z)))))))));
rule El _ ({|!_≡_|} $A $x0 $x) ↪ {|!TYPE___≡_|} $A (η (s 0ₙ z) $A $x0) (η (s 0ₙ z) $A $x);
constant symbol {|!_≡___refl|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, ({|!_≡_|} A (η (s 0ₙ z) A a) (η (s 0ₙ z) A a))))));
rule η _ ({|!_≡_|} _ _ _) ({|!_≡___refl|} $A $a) ↪ {|!_≡___refl|} $A (η (s 0ₙ z) $A $a);
 

constant symbol TYPE__Unit : TYPE;
constant symbol Unit : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ Unit ↪ TYPE__Unit;
constant symbol {|!Unit'constructor|} : El (set (s 0ₙ z)) Unit;
rule η _ Unit $y ↪ {|!Unit'constructor|};
 

symbol pro : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Unit (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Unit (λ y, ({|!_≡_|} Unit (η (s 0ₙ z) Unit x) (η (s 0ₙ z) Unit y))))));
rule pro $x $y ↪ η (s 0ₙ z) ({|!_≡_|} Unit (η (s 0ₙ z) Unit $x) (η (s 0ₙ z) Unit $y)) ({|!_≡___refl|} Unit (η (s 0ₙ z) Unit {|!Unit'constructor|}));
 
constant symbol TYPE__Uni : TYPE;
constant symbol Uni : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ Uni ↪ TYPE__Uni;
constant symbol Uni__I : El (set (s 0ₙ z)) Uni;
rule η _ Uni Uni__I ↪ Uni__I;
 

