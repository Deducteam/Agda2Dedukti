

// Nat to count succesors 
constant symbol ℕ : TYPE;
constant symbol 0ₙ : ℕ; builtin "0" ≔ 0ₙ;
constant symbol sₙ : ℕ → ℕ; builtin "+1" ≔ sₙ;

// max function on natural numbers
symbol ⊕ₙ : ℕ → ℕ → ℕ; notation ⊕ₙ infix right 10;

rule 0ₙ ⊕ₙ $y ↪ $y
with $x ⊕ₙ 0ₙ ↪ $x
with sₙ $x ⊕ₙ sₙ $y ↪ sₙ ($x ⊕ₙ $y);

// addition on natural numbers

symbol + : ℕ → ℕ → ℕ; notation + infix right 5;

rule 0ₙ + $y ↪ $y
with $x + 0ₙ ↪ $x
with sₙ $x + $y ↪ sₙ ($x + $y)
with $x + sₙ $y ↪ sₙ ($x + $y)
with ($x + $y) + $z ↪ $x + ($y + $z);

constant symbol IntLvl : TYPE;
constant symbol z : IntLvl;
symbol s : ℕ → IntLvl → IntLvl;
associative commutative symbol ⊕ : IntLvl → IntLvl → IntLvl; // associative right by default
notation ⊕ infix right 10;


rule s 0 z ⊕ $x ↪ $x
with $x ⊕ s 0 z ↪ $x;

rule $x ⊕ $x ↪ $x
with $x ⊕ ($x ⊕ $y)  ↪ $x ⊕ $y;

rule s $p (s $q $x) ↪ s ($p + $q) $x
with s $p ($x ⊕ $y) ↪ s $p $x ⊕ s $p $y;

rule s $p $x ⊕ s $q $x ↪ s ($p ⊕ₙ $q) $x
with s $p $x ⊕ (s $q $x ⊕ $y) ↪ s ($p ⊕ₙ $q) $x ⊕ $y;

// example
//compute λ a b c, (s 2 z ⊕ s 1 a) ⊕ s 0 b ⊕ (s 2 c ⊕ (s 1 a ⊕ z) ⊕ s 1 c);


//compute λ x, s 0 x ⊕ (s 0 z ⊕ s 0 z);




