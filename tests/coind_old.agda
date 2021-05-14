open import Agda.Builtin.Coinduction

data Coℕ : Set where
   zero : Coℕ
   suc  : ∞ Coℕ → Coℕ

inf : Coℕ
inf = suc (♯ inf)

