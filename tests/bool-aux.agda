open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

not : Bool → Bool
not true  = false
not false = true

_∨_ : Bool → Bool → Bool
true  ∨ x = true
false ∨ x = x

_∧_ : Bool → Bool → Bool
true  ∧ x = x
false ∧ x = false

infix 19 if_then_else_
if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

∨-assoc : (a b c : Bool) → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
∨-assoc true  _ _ = refl
∨-assoc false _ _ = refl

∧-assoc : (a b c : Bool) → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
∧-assoc true  _ _ = refl
∧-assoc false _ _ = refl

∨-comm : (a b : Bool) → a ∨ b ≡ b ∨ a
∨-comm true  true  = refl
∨-comm true  false = refl
∨-comm false true  = refl
∨-comm false false = refl

∨-cong : {a' b' : Bool} → (a b : Bool) → a ≡ a' → b ≡ b' → a ∨ b ≡ a' ∨ b'
∨-cong a b refl refl = refl

∧-comm : (a b : Bool) → a ∧ b ≡ b ∧ a
∧-comm true  true  = refl
∧-comm true  false = refl
∧-comm false true  = refl
∧-comm false false = refl


∨-idem : (a : Bool) → a ∨ a ≡ a
∨-idem true  = refl
∨-idem false = refl

∧-idem : (a : Bool) → a ∧ a ≡ a
∧-idem true  = refl
∧-idem false = refl

∧-cong : {a' b' : Bool} → (a b : Bool) → a ≡ a' → b ≡ b' → a ∧ b ≡ a' ∧ b'
∧-cong a b refl refl = refl


∨-∧-dist : (a b c : Bool) → a ∨ (b ∧ c) ≡ (a ∨ b) ∧ (a ∨ c)
∨-∧-dist true _ _ = refl
∨-∧-dist false _ _ = refl

∧-∨-dist : (a b c : Bool) → a ∧ (b ∨ c) ≡ (a ∧ b) ∨ (a ∧ c)
∧-∨-dist true _ _ = refl
∧-∨-dist false _ _ = refl

∨-comp : (a : Bool) → a ∨ (not a) ≡ true
∨-comp true = refl
∨-comp false = refl

∧-comp : (a : Bool) → a ∧ (not a) ≡ false
∧-comp true = refl
∧-comp false = refl
