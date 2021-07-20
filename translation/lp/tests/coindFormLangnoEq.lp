require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Bool as Agda__Builtin__Bool;
constant symbol TYPE__List : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol List : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⋄ (set (s 0ₙ z)))));
rule El _ (List $A) ↪ TYPE__List $A;
constant symbol {|!List___∷_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (List A) (λ _0, (List A)))))));
constant symbol {|!List__[]|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (List A)));
rule η _ (List _) ({|!List___∷_|} $A $x0 $x) ↪ {|!List___∷_|} $A (η (s 0ₙ z) $A $x0) (η (s 0ₙ z) (List $A) $x);
rule η _ (List _) ({|!List__[]|} $A) ↪ {|!List__[]|} $A;
 


constant symbol {|!TYPE___≡_|} : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π _0 : El (set (s 0ₙ z)) A, Π _0 : El (set (s 0ₙ z)) A, TYPE;
constant symbol {|!_≡_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z)))))))));
rule El _ ({|!_≡_|} $A $x0 $x) ↪ {|!TYPE___≡_|} $A (η (s 0ₙ z) $A $x0) (η (s 0ₙ z) $A $x);
constant symbol {|!_≡___refl|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, ({|!_≡_|} A (η (s 0ₙ z) A a) (η (s 0ₙ z) A a))))));
rule η _ ({|!_≡_|} _ _ _) ({|!_≡___refl|} $A $a) ↪ {|!_≡___refl|} $A (η (s 0ₙ z) $A $a);
 

symbol not : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ _0, Agda__Builtin__Bool.Bool));
rule not Agda__Builtin__Bool.Bool__false ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true;
rule not Agda__Builtin__Bool.Bool__true ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false;
 
symbol {|!_∨_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ _0, Agda__Builtin__Bool.Bool))));
rule {|!_∨_|} Agda__Builtin__Bool.Bool__false $x ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool $x;
rule {|!_∨_|} Agda__Builtin__Bool.Bool__true $x ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true;
 
symbol sym : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ b, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≡_|} A (η (s 0ₙ z) A a) (η (s 0ₙ z) A b)) (λ _0, ({|!_≡_|} A (η (s 0ₙ z) A b) (η (s 0ₙ z) A a))))))))));
rule sym $A $a _ ({|!_≡___refl|} _ _) ↪ η (s 0ₙ z) ({|!_≡_|} $A (η (s 0ₙ z) $A $a) (η (s 0ₙ z) $A $a)) ({|!_≡___refl|} $A (η (s 0ₙ z) $A $a));
 
symbol trans : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ {|!z|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≡_|} A (η (s 0ₙ z) A x) (η (s 0ₙ z) A y)) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≡_|} A (η (s 0ₙ z) A y) (η (s 0ₙ z) A {|!z|})) (λ _0, ({|!_≡_|} A (η (s 0ₙ z) A x) (η (s 0ₙ z) A {|!z|}))))))))))))));
rule trans $A $x0 $y _ $x ({|!_≡___refl|} _ _) ↪ η (s 0ₙ z) ({|!_≡_|} $A (η (s 0ₙ z) $A $x0) (η (s 0ₙ z) $A $y)) $x;
 
symbol {|!∨-assoc|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ b, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ c, ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool a) (η (s 0ₙ z) Agda__Builtin__Bool.Bool b))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool c))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool a) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool b) (η (s 0ₙ z) Agda__Builtin__Bool.Bool c))))))))))));
rule {|!∨-assoc|} Agda__Builtin__Bool.Bool__false $b $c ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false) (η (s 0ₙ z) Agda__Builtin__Bool.Bool $b))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool $c))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool $b) (η (s 0ₙ z) Agda__Builtin__Bool.Bool $c)))))) ({|!_≡___refl|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false) (η (s 0ₙ z) Agda__Builtin__Bool.Bool $b))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool $c))));
rule {|!∨-assoc|} Agda__Builtin__Bool.Bool__true $b $c ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true) (η (s 0ₙ z) Agda__Builtin__Bool.Bool $b))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool $c))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool $b) (η (s 0ₙ z) Agda__Builtin__Bool.Bool $c)))))) ({|!_≡___refl|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true) (η (s 0ₙ z) Agda__Builtin__Bool.Bool $b))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool $c))));
 
symbol {|!∨-comm|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ b, ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool a) (η (s 0ₙ z) Agda__Builtin__Bool.Bool b))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool b) (η (s 0ₙ z) Agda__Builtin__Bool.Bool a))))))));
rule {|!∨-comm|} Agda__Builtin__Bool.Bool__false Agda__Builtin__Bool.Bool__false ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false)))) ({|!_≡___refl|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false))));
rule {|!∨-comm|} Agda__Builtin__Bool.Bool__false Agda__Builtin__Bool.Bool__true ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false)))) ({|!_≡___refl|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true))));
rule {|!∨-comm|} Agda__Builtin__Bool.Bool__true Agda__Builtin__Bool.Bool__false ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true)))) ({|!_≡___refl|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false))));
rule {|!∨-comm|} Agda__Builtin__Bool.Bool__true Agda__Builtin__Bool.Bool__true ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true)))) ({|!_≡___refl|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true))));
 
symbol {|!∨-idem|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ a, ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool a) (η (s 0ₙ z) Agda__Builtin__Bool.Bool a))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool a))));
rule {|!∨-idem|} Agda__Builtin__Bool.Bool__false ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false)) ({|!_≡___refl|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false))));
rule {|!∨-idem|} Agda__Builtin__Bool.Bool__true ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true)) ({|!_≡___refl|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true) (η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true))));
 
constant symbol TYPE__Lang : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol Lang : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⋄ (set (s 0ₙ z)))));
rule El _ (Lang $A) ↪ TYPE__Lang $A;
symbol {|!Lang__ν|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ r, Agda__Builtin__Bool.Bool))));
symbol {|!Lang__δ|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ r, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, (Lang A)))))));
constant symbol {|!Lang'constructor|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ {|!ν|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, (Lang A))) (λ {|!δ|}, (Lang A)))))));
rule η _ (Lang $A) $y ↪ $y;
 
rule {|!Lang__ν|} $A ({|!Lang'constructor|} _ ${|!ν|} ${|!δ|}) ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool ${|!ν|};
 
rule {|!Lang__δ|} $A ({|!Lang'constructor|} _ ${|!ν|} ${|!δ|}) ↪ λ _0, ${|!δ|} (η (s 0ₙ z) $A _0);
 

symbol {|!_∈_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (List A) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, Agda__Builtin__Bool.Bool))))));
rule {|!_∈_|} $A ({|!List___∷_|} _ $x1 $x0) $x ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∈_|} $A (η (s 0ₙ z) (List $A) $x0) ({|!Lang__δ|} $A $x (η (s 0ₙ z) $A $x1)));
rule {|!_∈_|} $A ({|!List__[]|} _) $x ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $x);
 
symbol trie : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (List A) (λ _0, Agda__Builtin__Bool.Bool)) (λ f, (Lang A)))));
rule {|!Lang__ν|} _ (trie $A $f) ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool ($f (η (s 0ₙ z) (List $A) ({|!List__[]|} $A)));
rule {|!Lang__δ|} _ (trie $A $f) $x ↪ trie $A (λ ls, η (s 0ₙ z) Agda__Builtin__Bool.Bool ($f (η (s 0ₙ z) (List $A) ({|!List___∷_|} $A (η (s 0ₙ z) $A $x) (η (s 0ₙ z) (List $A) ls)))));
 
symbol {|!∅|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (Lang A)));
rule {|!Lang__ν|} _ ({|!∅|} $A) ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false;
rule {|!Lang__δ|} _ ({|!∅|} $A) $x ↪ {|!∅|} $A;
 
symbol {|!ε|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (Lang A)));
rule {|!Lang__ν|} _ ({|!ε|} $A) ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true;
rule {|!Lang__δ|} _ ({|!ε|} $A) $x ↪ {|!∅|} $A;
 
symbol {|!¬|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (Lang A)))));
rule {|!Lang__ν|} _ ({|!¬|} $A $x) ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool (not (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $x)));
rule {|!Lang__δ|} _ ({|!¬|} $A $x0) $x ↪ {|!¬|} $A ({|!Lang__δ|} $A $x0 (η (s 0ₙ z) $A $x));
 
symbol {|!_∪_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (Lang A)))))));
rule {|!Lang__ν|} _ ({|!_∪_|} $A $x0 $x) ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $x0)) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $x)));
rule {|!Lang__δ|} _ ({|!_∪_|} $A $x1 $x0) $x ↪ {|!_∪_|} $A ({|!Lang__δ|} $A $x1 (η (s 0ₙ z) $A $x)) ({|!Lang__δ|} $A $x0 (η (s 0ₙ z) $A $x));
 
constant symbol {|!TYPE___≈_|} : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π l : El (set (s 0ₙ z)) (Lang A), Π {|!s|} : El (set (s 0ₙ z)) (Lang A), TYPE;
constant symbol {|!_≈_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) (Lang A) (λ {|!s|}, (⋄ (set (s 0ₙ z)))))))));
rule El _ ({|!_≈_|} $A $l ${|!s|}) ↪ {|!TYPE___≈_|} $A $l ${|!s|};
symbol {|!_≈___≈ν|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A l {|!s|}) (λ r, ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} A l)) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} A {|!s|})))))))))));
symbol {|!_≈___≈δ|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A l {|!s|}) (λ r, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, ({|!_≈_|} A ({|!Lang__δ|} A l (η (s 0ₙ z) A a)) ({|!Lang__δ|} A {|!s|} (η (s 0ₙ z) A a)))))))))))));
constant symbol {|!_≈_'constructor|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} A l)) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} A {|!s|}))) (λ {|!≈ν|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, ({|!_≈_|} A ({|!Lang__δ|} A l (η (s 0ₙ z) A a)) ({|!Lang__δ|} A {|!s|} (η (s 0ₙ z) A a))))) (λ {|!≈δ|}, ({|!_≈_|} A l {|!s|})))))))))));
rule η _ ({|!_≈_|} $A $l ${|!s|}) $y ↪ $y;
 
rule {|!_≈___≈ν|} $A $l ${|!s|} ({|!_≈_'constructor|} _ _ _ ${|!≈ν|} ${|!≈δ|}) ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l)) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ${|!s|}))) ${|!≈ν|};
 
rule {|!_≈___≈δ|} $A $l ${|!s|} ({|!_≈_'constructor|} _ _ _ ${|!≈ν|} ${|!≈δ|}) ↪ λ a, ${|!≈δ|} (η (s 0ₙ z) $A a);
 

symbol {|!≈refl|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, ({|!_≈_|} A l l)))));
rule {|!_≈___≈ν|} _ _ _ ({|!≈refl|} $A $l) ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l)) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l))) ({|!_≡___refl|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l)));
rule {|!_≈___≈δ|} _ _ _ ({|!≈refl|} $A $l) $a ↪ {|!≈refl|} $A ({|!Lang__δ|} $A $l (η (s 0ₙ z) $A $a));
 
symbol {|!≈sym|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A l {|!s|}) (λ _0, ({|!_≈_|} A {|!s|} l)))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!≈sym|} $A $l ${|!s|} $x) ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ${|!s|})) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l))) (sym Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l)) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ${|!s|})) (η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l)) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ${|!s|}))) ({|!_≈___≈ν|} $A $l ${|!s|} $x)));
rule {|!_≈___≈δ|} _ _ _ ({|!≈sym|} $A $l ${|!s|} $x) $a ↪ {|!≈sym|} $A ({|!Lang__δ|} $A $l (η (s 0ₙ z) $A $a)) ({|!Lang__δ|} $A ${|!s|} (η (s 0ₙ z) $A $a)) ({|!_≈___≈δ|} $A $l ${|!s|} $x (η (s 0ₙ z) $A $a));
 
symbol {|!≈trans|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ k, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A l {|!s|}) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A {|!s|} k) (λ _0, ({|!_≈_|} A l k)))))))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!≈trans|} $A $l ${|!s|} $k $x0 $x) ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l)) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $k))) (trans Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l)) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ${|!s|})) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $k)) (η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l)) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ${|!s|}))) ({|!_≈___≈ν|} $A $l ${|!s|} $x0)) (η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ${|!s|})) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $k))) ({|!_≈___≈ν|} $A ${|!s|} $k $x)));
rule {|!_≈___≈δ|} _ _ _ ({|!≈trans|} $A $l ${|!s|} $k $x0 $x) $a ↪ {|!≈trans|} $A ({|!Lang__δ|} $A $l (η (s 0ₙ z) $A $a)) ({|!Lang__δ|} $A ${|!s|} (η (s 0ₙ z) $A $a)) ({|!Lang__δ|} $A $k (η (s 0ₙ z) $A $a)) ({|!_≈___≈δ|} $A $l ${|!s|} $x0 (η (s 0ₙ z) $A $a)) ({|!_≈___≈δ|} $A ${|!s|} $k $x (η (s 0ₙ z) $A $a));
 
symbol {|!∪-assoc|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ k, ({|!_≈_|} A ({|!_∪_|} A ({|!_∪_|} A l {|!s|}) k) ({|!_∪_|} A l ({|!_∪_|} A {|!s|} k)))))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!∪-assoc|} $A $l ${|!s|} $k) ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ({|!_∪_|} $A ({|!_∪_|} $A $l ${|!s|}) $k))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ({|!_∪_|} $A $l ({|!_∪_|} $A ${|!s|} $k))))) ({|!∨-assoc|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l)) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ${|!s|})) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $k)));
rule {|!_≈___≈δ|} _ _ _ ({|!∪-assoc|} $A $l ${|!s|} $k) $a ↪ {|!∪-assoc|} $A ({|!Lang__δ|} $A $l (η (s 0ₙ z) $A $a)) ({|!Lang__δ|} $A ${|!s|} (η (s 0ₙ z) $A $a)) ({|!Lang__δ|} $A $k (η (s 0ₙ z) $A $a));
 
symbol {|!∪-comm|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, ({|!_≈_|} A ({|!_∪_|} A l {|!s|}) ({|!_∪_|} A {|!s|} l))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!∪-comm|} $A $l ${|!s|}) ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ({|!_∪_|} $A $l ${|!s|}))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ({|!_∪_|} $A ${|!s|} $l)))) ({|!∨-comm|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l)) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ${|!s|})));
rule {|!_≈___≈δ|} _ _ _ ({|!∪-comm|} $A $l ${|!s|}) $a ↪ {|!∪-comm|} $A ({|!Lang__δ|} $A $l (η (s 0ₙ z) $A $a)) ({|!Lang__δ|} $A ${|!s|} (η (s 0ₙ z) $A $a));
 
symbol {|!∪-idem|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, ({|!_≈_|} A ({|!_∪_|} A l l) l)))));
rule {|!_≈___≈ν|} _ _ _ ({|!∪-idem|} $A $l) ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ({|!_∪_|} $A $l $l))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l))) ({|!∨-idem|} (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l)));
rule {|!_≈___≈δ|} _ _ _ ({|!∪-idem|} $A $l) $a ↪ {|!∪-idem|} $A ({|!Lang__δ|} $A $l (η (s 0ₙ z) $A $a));
 
symbol {|!∪-unit₁|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, ({|!_≈_|} A ({|!_∪_|} A ({|!∅|} A) l) l)))));
rule {|!_≈___≈ν|} _ _ _ ({|!∪-unit₁|} $A $l) ↪ η (s 0ₙ z) ({|!_≡_|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ({|!_∪_|} $A ({|!∅|} $A) $l))) (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l))) ({|!_≡___refl|} Agda__Builtin__Bool.Bool (η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ({|!_∪_|} $A ({|!∅|} $A) $l))));
rule {|!_≈___≈δ|} _ _ _ ({|!∪-unit₁|} $A $l) $a ↪ {|!∪-unit₁|} $A ({|!Lang__δ|} $A $l (η (s 0ₙ z) $A $a));
 
symbol {|!∪-unit₂|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, ({|!_≈_|} A ({|!_∪_|} A l ({|!∅|} A)) l)))));
rule {|!∪-unit₂|} $A $l ↪ {|!≈trans|} $A ({|!_∪_|} $A $l ({|!∅|} $A)) ({|!_∪_|} $A ({|!∅|} $A) $l) $l ({|!∪-comm|} $A $l ({|!∅|} $A)) ({|!∪-unit₁|} $A $l);
 
