// Levels
require open AgdaTheory.Levels;

// Sorts
constant symbol Sort : TYPE;
constant symbol U : Sort → TYPE;
constant symbol set : L → Sort;
constant symbol prop : L → Sort;
constant symbol setω : Sort;

// Rule
symbol ∨ : Sort → Sort → Sort;
rule ∨ (set $i)  (set $j)  ↪ set  ($i ⊕ $j)
with ∨ (prop $i) (prop $j) ↪ prop ($i ⊕ $j)
with ∨ (set $i)  (prop $j) ↪ prop ($i ⊕ $j)
with ∨ (prop $i) (set $j)  ↪ set  ($i ⊕ $j)
with ∨ _         setω      ↪ setω;

// Axiom
symbol □ : Sort → Sort;
rule □ (set $i)   ↪ set (s (sₙ 0ₙ) $i)
with □ (prop $i)  ↪ set (s (sₙ 0ₙ) $i);

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
rule El _ (⇝     (set  $i) $s' $A $B) ↪ Π (x : El (set  $i) $A), El $s' ($B x)
with El _ (⇝     (prop $i) $s' $A $B) ↪ Π (x : El (prop $i) $A), El $s' ($B x);

constant symbol ⇝proj : Π (s s' : Sort) (A : U s), (El s A → U s') → U (∨ s s');
rule El _ (⇝proj $s        $s' $A $B) ↪ Π (x : El $s $A), El $s' ($B x);




