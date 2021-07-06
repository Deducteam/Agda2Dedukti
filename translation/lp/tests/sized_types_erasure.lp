require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Bool as Agda__Builtin__Bool;
require tests.Agda__Builtin__List as Agda__Builtin__List;
symbol boolOr : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ _0, Agda__Builtin__Bool.Bool))));
rule boolOr Agda__Builtin__Bool.Bool__false $x ↪ $x;
rule boolOr Agda__Builtin__Bool.Bool__true $x ↪ Agda__Builtin__Bool.Bool__true;
 
symbol boolAnd : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ _0, Agda__Builtin__Bool.Bool))));
rule boolAnd Agda__Builtin__Bool.Bool__false $x ↪ Agda__Builtin__Bool.Bool__false;
rule boolAnd Agda__Builtin__Bool.Bool__true $x ↪ $x;
 
symbol if_then_else_ : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, A))))))));
rule if_then_else_ $A Agda__Builtin__Bool.Bool__false $x0 $x ↪ $x;
rule if_then_else_ $A Agda__Builtin__Bool.Bool__true $x0 $x ↪ $x0;
 
constant symbol TYPE__Lang : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol Lang : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⋄ (set (s 0ₙ z)))));
rule El _ (Lang $A) ↪ TYPE__Lang $A;
symbol {|!Lang__ν|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ r, Agda__Builtin__Bool.Bool))));
symbol {|!Lang__δ|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ r, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, (Lang A)))))));
constant symbol {|!Lang'constructor|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ {|!ν|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, (Lang A))) (λ {|!δ|}, (Lang A)))))));

rule {|!Lang__ν|} $A ({|!Lang'constructor|} _ ${|!ν|} ${|!δ|}) ↪ ${|!ν|};
 
rule {|!Lang__δ|} $A ({|!Lang'constructor|} _ ${|!ν|} ${|!δ|}) ↪ ${|!δ|};
 

symbol {|!∅|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (Lang A)));
rule {|!Lang__ν|} _ ({|!∅|} $A) ↪ Agda__Builtin__Bool.Bool__false;
rule {|!Lang__δ|} _ ({|!∅|} $A) $x ↪ {|!∅|} $A;
 
symbol {|!ε|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (Lang A)));
rule {|!Lang__ν|} _ ({|!ε|} $A) ↪ Agda__Builtin__Bool.Bool__true;
rule {|!Lang__δ|} _ ({|!ε|} $A) $x ↪ {|!∅|} $A;
 
symbol {|!_+_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (Lang A)))))));
rule {|!Lang__ν|} _ ({|!_+_|} $A $x0 $x) ↪ boolOr ({|!Lang__ν|} $A $x0) ({|!Lang__ν|} $A $x);
rule {|!Lang__δ|} _ ({|!_+_|} $A $x1 $x0) $x ↪ {|!_+_|} $A ({|!Lang__δ|} $A $x1 $x) ({|!Lang__δ|} $A $x0 $x);
 
symbol {|!_·_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (Lang A)))))));
rule {|!Lang__ν|} _ ({|!_·_|} $A $x0 $x) ↪ boolAnd ({|!Lang__ν|} $A $x0) ({|!Lang__ν|} $A $x);
rule {|!Lang__δ|} _ ({|!_·_|} $A $x1 $x0) $x ↪ if_then_else_ (Lang $A) ({|!Lang__ν|} $A $x1) ({|!_+_|} $A ({|!_·_|} $A ({|!Lang__δ|} $A $x1 $x) $x0) ({|!Lang__δ|} $A $x0 $x)) ({|!_·_|} $A ({|!Lang__δ|} $A $x1 $x) $x0);
 
symbol {|!_*|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (Lang A)))));
rule {|!Lang__ν|} _ ({|!_*|} $A $x) ↪ Agda__Builtin__Bool.Bool__true;
rule {|!Lang__δ|} _ ({|!_*|} $A $x0) $x ↪ {|!_·_|} $A ({|!Lang__δ|} $A $x0 $x) ({|!_*|} $A $x0);
 
symbol {|!_∈_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__List.List (s 0ₙ z) A) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, Agda__Builtin__Bool.Bool))))));
rule {|!_∈_|} $A (Agda__Builtin__List.{|!List__[]|} _ _) $x ↪ {|!Lang__ν|} $A $x;
rule {|!_∈_|} $A (Agda__Builtin__List.{|!List___∷_|} _ _ $x1 $x0) $x ↪ {|!_∈_|} $A $x0 ({|!Lang__δ|} $A $x $x1);
 
