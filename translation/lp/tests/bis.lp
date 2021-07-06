require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Equality as Agda__Builtin__Equality;
require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
constant symbol {|!TYPE__⊥|} : TYPE;
constant symbol {|!⊥|} : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ {|!⊥|} ↪ {|!TYPE__⊥|};

constant symbol {|!TYPE__∨|} : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π B : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol {|!∨|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ B, (⋄ (set (s 0ₙ z)))))));
rule El _ ({|!∨|} $A $B) ↪ {|!TYPE__∨|} $A $B;
constant symbol {|!∨__inl|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, ({|!∨|} A B)))))));
constant symbol {|!∨__inr|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) B (λ _0, ({|!∨|} A B)))))));



constant symbol TYPE__Node : TYPE;
constant symbol Node : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ Node ↪ TYPE__Node;
symbol Node__value : El (set (s 0ₙ z)) (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) Node (λ r, Agda__Builtin__Nat.Nat));
symbol Node__edge : El (set (s 0ₙ z)) (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) Node (λ r, Node));
constant symbol {|!Node'constructor|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ value, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Node (λ edge, Node))));

rule Node__value ({|!Node'constructor|} $value $edge) ↪ $value;
 
rule Node__edge ({|!Node'constructor|} $value $edge) ↪ $edge;
 

symbol g1 : El (set (s 0ₙ z)) Node;
symbol g2 : El (set (s 0ₙ z)) Node;
rule Node__value g1 ↪ Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero;
rule Node__edge g1 ↪ g2;
 
rule Node__value g2 ↪ Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero;
rule Node__edge g2 ↪ g1;
 
symbol g3 : El (set (s 0ₙ z)) Node;
rule Node__value g3 ↪ Agda__Builtin__Nat.Nat__suc Agda__Builtin__Nat.Nat__zero;
rule Node__edge g3 ↪ g3;
 
constant symbol TYPE__Bissim : Π A : El (set (s 0ₙ z)) Node, Π B : El (set (s 0ₙ z)) Node, TYPE;
constant symbol Bissim : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) Node (λ A, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) Node (λ B, (⋄ (set (s 0ₙ z)))))));
rule El _ (Bissim $A $B) ↪ TYPE__Bissim $A $B;
symbol Bissim__eqv : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Node (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Node (λ B, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Bissim A B) (λ r, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Nat.Nat (Node__value A) (Node__value B))))))));
symbol Bissim__eqt : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Node (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Node (λ B, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Bissim A B) (λ r, (Bissim (Node__edge A) (Node__edge B))))))));
constant symbol {|!Bissim'constructor|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Node (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Node (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Nat.Nat (Node__value A) (Node__value B)) (λ eqv, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Bissim (Node__edge A) (Node__edge B)) (λ eqt, (Bissim A B)))))))));

rule Bissim__eqv $A $B ({|!Bissim'constructor|} _ _ $eqv $eqt) ↪ $eqv;
 
rule Bissim__eqt $A $B ({|!Bissim'constructor|} _ _ $eqv $eqt) ↪ $eqt;
 

symbol bis1 : El (set (s 0ₙ z)) (Bissim g1 g3);
symbol bis2 : El (set (s 0ₙ z)) (Bissim g2 g3);
rule Bissim__eqv _ _ bis1 ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Nat.Nat (Node__value g1);
rule Bissim__eqt _ _ bis1 ↪ bis2;
 
rule Bissim__eqv _ _ bis2 ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Nat.Nat (Node__value g2);
rule Bissim__eqt _ _ bis2 ↪ bis1;
 
