// Levels
symbol L : TYPE;
symbol O : L;
symbol S : L → L;
symbol ⊔ : L → L → L;

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
rule □ (set $i)   ↪ set (S $i)
with □ (prop $i)  ↪ set (S $i);

// Terms
symbol El : Π (s : Sort), U s → TYPE;

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
symbol η : Π (l : L) (A : U (set l)), El (set l) A → El (set l) A;

rule El _ (⇝     (set  $i) $s' $A $B) ↪ Π (x : El (set  $i) $A), El $s' ($B (η $i $A x))
with El _ (⇝     (prop $i) $s' $A $B) ↪ Π (x : El (prop $i) $A), El $s' ($B x)
with El _ (⇝proj $s        $s' $A $B) ↪ Π (x : El $s $A), El $s' ($B x);

rule η _ _ (η $l $A $x) ↪ η $l $A $x
with η _ (⋄ _) $x ↪ $x;

rule η _ (⇝     (set  $i) (set $j) $A $B) $f ↪ λ (x : El (set  $i) $A), η $j ($B (η $i $A x)) ($f (η $i $A x))
with η _ (⇝     (prop $i) (set $j) $A $B) $f ↪ λ (x : El (prop $i) $A), η $j ($B x) ($f x)
with η _ (⇝proj $s        (set $j) $A $B) $f ↪ λ (x : El $s       $A), η $j ($B x) ($f x);

require open AgdaTheory.Levels;

// agda's level syntax is translated into the ⊕ algebra 
rule L         ↪ IntLvl;
rule O         ↪ s 0 z
with S $x      ↪ s 1 ($x ⊕ z)
with ⊔ $x $y   ↪ $x ⊕ $y;
