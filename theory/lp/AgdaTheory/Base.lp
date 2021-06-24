// Levels
symbol L : TYPE;
symbol o : L;
symbol s : L → L;
symbol ⊔ : L → L → L;
symbol ⋕ : L → L; 

// Sorts
constant symbol Sort : TYPE;
constant symbol U : Sort → TYPE;
constant symbol set : L → Sort;
constant symbol prop : L → Sort;
constant symbol setω : Sort;

// Rule
symbol ∨ : Sort → Sort → Sort;
rule ∨ (set $i)  (set $j)  ↪ set  (⊔ $i $j)
with ∨ (prop $i) (prop $j) ↪ prop (⊔ $i $j)
with ∨ (set $i)  (prop $j) ↪ prop (⊔ $i $j)
with ∨ (prop $i) (set $j)  ↪ set  (⊔ $i $j)
with ∨ _         setω      ↪ setω;

// Axiom
symbol □ : Sort → Sort;
rule □ (set $i)   ↪ set (s $i)
with □ (prop $i)  ↪ set (s $i);

// Terms (injective ?)
injective symbol El : Π (s : Sort), U s → TYPE;

// Sort inclusion
constant symbol ⋄ : Π (s : Sort), U (□ s);
rule El _ (⋄ $s) ↪ U $s; 

// Universe Polymorphism
constant symbol ∀ : Π α : L → Sort, (Π (i : L), U (α i)) → U setω;
rule El _ (∀ $α $A) ↪ Π (i : L), El ($α i) ($A i);

// Products
constant symbol ⇝ : Π (s s' : Sort) (A : U s), (El s A → U s') → U (∨ s s');
constant symbol ⇝proj : Π (s s' : Sort) (A : U s), (El s A → U s') → U (∨ s s');

// etaExpand
injective symbol η : Π (l : L) (A : U (set l)), El (set l) A → El (set l) A;

rule El _ (⇝     (set  $i) $s' $A $B) ↪ Π (x : El (set  $i) $A), El $s' ($B (η $i $A x))
with El _ (⇝     (prop $i) $s' $A $B) ↪ Π (x : El (prop $i) $A), El $s' ($B x)
with El _ (⇝proj $s        $s' $A $B) ↪ Π (x : El $s $A), El $s' ($B x);

rule η _ _ (η $l $A $x) ↪ η $l $A $x
with η _ (⋄ _) $x ↪ $x;

rule η _ (⇝     (set  $i) (set $j) $A $B) $f ↪ λ (x : El (set  $i) $A), η $j ($B (η $i $A x)) ($f (η $i $A x))
with η _ (⇝     (prop $i) (set $j) $A $B) $f ↪ λ (x : El (prop $i) $A), η $j ($B x) ($f x)
with η _ (⇝proj $s        (set $j) $A $B) $f ↪ λ (x : El $s       $A), η $j ($B x) ($f x);

require AgdaTheory.Levels as Lvl;

// for the time being, because lp is broken, we dont deal with univ poly
rule ⊔ $x o ↪ $x
with ⊔ o $y ↪ $y
with ⊔ (s $x) (s $y) ↪ s (⊔ $x $y);

// agda's level syntax is translated into the ⊕ algebra 
//rule L         ↪ Lvl.IntLvl;
//rule o         ↪ Lvl.s Lvl.0ₙ Lvl.z
//with s $x      ↪ Lvl.s (Lvl.sₙ Lvl.0ₙ) $x
//with ⋕ $x      ↪ Lvl.s Lvl.0ₙ (Lvl.⊕ $x Lvl.z)
//with ⊔ $x $y   ↪ Lvl.⊕ $x $y;

// tests

compute λ x y, ⊔ (⊔ (s (s (⋕ x))) (s (⋕ y))) o;
compute λ x y, ⊔ (⊔ (s (⋕ y)) (s (s (⋕ x)))) (s o);
compute λ x y, s (⊔ (⋕ y) (⊔ (s (⋕ x)) o));
compute λ x y, ⊔ (s (s (⊔ (⋕ x) o))) (s (⋕ y));
compute λ x y, ⊔ (⊔ (s (s (⋕ x))) (s (⋕ y))) (s (s o));

compute λ x y, ⊔ (⋕ x) (s (⊔ (⋕ y) (s (⋕ x))));

compute λ x, ⊔ (⋕ x) o;

compute λ x, ⊔ o (⋕ x);

compute λ x, ⊔ o (⊔ (⊔ (⋕ x) (⊔ (s o) o)) (⊔ o (⊔ (⋕ x) (⋕ x))));

compute λ x, (⋕ x);

