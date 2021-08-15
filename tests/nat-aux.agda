open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import eq-aux


z-+ : (x : Nat) -> x + zero ≡ x
z-+ zero = refl
z-+ (suc n) = cong suc (z-+ n)

+-assoc : (x y z : Nat) -> (x + y) + z ≡ x + (y + z)
+-assoc 0 y z = refl
+-assoc (suc x) y z = cong suc (+-assoc x y z)

+-com : (x y : Nat) -> x + y ≡ y + x
+-com zero y = sym (z-+ y)
+-com (suc x) zero = z-+ (suc x)
+-com (suc x) (suc y) = trans (trans (cong suc (+-com x (suc y))) (cong (λ x → suc (suc x)) (+-com y x))) (cong suc (+-com (suc x) y))

