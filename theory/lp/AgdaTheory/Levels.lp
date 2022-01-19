

// Nat to count succesors 
constant symbol ℕ : TYPE;
constant symbol 0ₙ : ℕ;// builtin "0" ≔ 0ₙ;
constant symbol sₙ : ℕ → ℕ; //builtin "+1" ≔ sₙ;

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

constant symbol L : TYPE;
constant symbol z : L;
symbol s : ℕ → L → L;
associative commutative symbol ⊕ : L → L → L; // associative right by default
notation ⊕ infix right 10;

rule s $p (s $q $x) ↪ s ($p + $q) $x
with s $p ($x ⊕ $y) ↪ s $p $x ⊕ s $p $y;

rule s $p $x ⊕ s $q $x ↪ s ($p ⊕ₙ $q) $x
with s $p $x ⊕ (s $q $x ⊕ $y) ↪ s ($p ⊕ₙ $q) $x ⊕ $y;





