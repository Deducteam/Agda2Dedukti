data false : Set where

fimp : (A : Set) → false → A
fimp a ()

data exists : (A : Set) → (P : A → Set) → Set where
  exintro : {A : Set} → {P : A → Set} → (a : A) → (p : P a) → exists A P

data or : Set → Set → Set where
  orl : {A B : Set} → (a : A) → or A B
  orr : {A B : Set} → (b : B) → or A B  

data and : Set → Set → Set where
  inand : {A B : Set} → (a : A) → (b : B) → and A B

data N : Set where
  zero : N
  suc : N → N

data Neq : N → N → Set where
  refl : (x : N) → Neq x x

-- equality is a congruence --
cong : {x y : N} → (Neq x y) → (f : N → N) → (Neq (f x) (f y))
cong (refl a) f = refl (f a)

sym : {x y : N} → (Neq x y) → (Neq y x)
sym (refl a) = refl a

trs : {x y z : N} → (Neq x y) → (Neq y z) → (Neq x z)
trs (refl a) (refl b) = refl a

-- zero is no successor --
suc0 : (x : N) → Neq (suc x) zero → false
suc0 x ()

-- sum --
sum : N → N → N
sum zero y = y
sum (suc x) y = suc (sum x y)

sum0 : (x : N) → (Neq x (sum x zero))
sum0 zero = refl zero
sum0 (suc x) = cong (sum0 x) suc

sumassos : {x y z : N} → Neq (sum x (sum y z)) (sum (sum x y) z)
sumassos {zero} {y} {z} = refl (sum y z)
sumassos {suc x} {y} {z} with (sumassos {x} {y} {z})
sumassos {suc x} {y} {z}  | p = cong p suc

sumcom : {x y : N} → Neq (sum x y) (sum y x)
sumcom {zero} {zero} = refl zero
sumcom {zero} {y} = sum0 y
sumcom {x} {zero} = sym (sum0 x)
sumcom {suc x} {suc y} = cong (trs (sumcom {x} {suc y}) (trs (cong (sumcom {y} {x}) suc) (sumcom {suc x} {y}))) suc

-- multiplication
mult : N → N → N
mult zero y = zero
mult (suc x) y = sum y (mult x y)

mult0 : (x : N) → Neq zero (mult x zero)
mult0 zero = refl zero
mult0 (suc x) = mult0 x

multcom : {x y : N} → (Neq (mult x y) (mult y x))
multcom {zero} {zero} = refl zero
multcom {zero} {y} = mult0 y
multcom {x} {zero} = sym (mult0 x)
multcom {suc x} {suc y} = cong (trs (cong (multcom {x} {suc y}) (λ a → sum y a)) (trs (trs (sumassos {y} {x} {mult y x}) (trs (trs (cong (sumcom {y} {x}) (λ a → sum a (mult y x))) (cong (multcom {y} {x}) (λ a → sum (sum x y) a))) (sym (sumassos {x} {y} {mult x y})))) (cong (multcom {suc x} {y}) (λ a → sum x a)))) suc



data Nleq : N → N → Set where
  0leq : {x : N} → Nleq zero x
  Sleq : {x y : N} → Nleq x y →  Nleq (suc x) (suc y)

-- excluded middle for inequality --
exm : {x y : N} → or (Nleq x y) (Nleq x y → false)
exm {zero} {y} = orl 0leq
exm {suc x} {zero} = orr λ ()
exm {suc x} {suc y} with (exm {x} {y})
exm {suc x} {suc y}   | orl a = orl (Sleq a)
exm {suc x} {suc y}   | orr b = orr (λ { (Sleq z) → b z})


-- inequality = equality or strict ineq --
strictornot : (x y : N) → (Nleq x y) → (or (Neq x y) (Nleq (suc x) y))
strictornot zero zero p = orl (refl zero)
strictornot zero (suc y) p = orr (Sleq 0leq)
strictornot (suc x) zero ()
strictornot (suc x) (suc y) (Sleq p) with (strictornot x y p)
strictornot (suc x) (suc .x) (Sleq p) | orl (refl x) = orl (refl (suc x))
strictornot (suc x) (suc y) (Sleq p) | orr b = orr (Sleq b)

-- minus function --
minus : (x : N) → (y : N) → (p : Nleq y x) →
  (exists N (λ a → Neq x (sum y a)))
minus zero (suc y) ()
minus (suc y) zero p = exintro (suc y) (refl (suc y))
minus zero zero _ = exintro zero (refl zero)
minus (suc x) (suc y) (Sleq p) with (minus x y p)
minus (suc x) (suc y) (Sleq p)   | exintro a p2 = exintro a (cong p2 suc)


-- euclidian division --
euclid : (x : N) → (y : N) → (p : Neq y zero → false) →
  (exists N (λ p →
    (exists N (λ r →
      and (Nleq (suc r) (y)) (Neq x (sum (mult y p) r))  ))))

euclid x zero p = fimp _ (p (refl zero))
euclid zero (suc y) p = exintro zero
                        (exintro zero
                        (inand (Sleq 0leq) (trs (mult0 y) (sum0 (mult y zero)))))

euclid (suc x) y p with (euclid x y p)

euclid (suc x) y p | exintro a (exintro a2 (inand b1 b2)) with (strictornot _ _ b1)

euclid (suc x) y p | exintro a (exintro a2 (inand b1 b2))  | orr j =
  exintro a (exintro (suc a2) (inand j
    (trs (cong (trs b2 (sumcom {mult y a} {a2})) suc) (sumcom {suc a2} {mult y a}))))

euclid (suc .(sum (sum a (mult y a)) y)) (suc y) p | exintro a (exintro y (inand b1 (refl .(sum (sum a (mult y a)) y)))) | orl (refl .(suc y)) =
  exintro (suc a) (exintro zero (inand (Sleq 0leq)
    (cong (trs (trs (sym (sumassos {a} {mult y a} {y})) (cong (trs (sumcom {mult y a} {y}) (trs (cong (multcom {y} {a}) (λ s → sum y s)) (multcom {suc a} {y}))) (λ s → sum a s))) (sum0 (sum a (mult y (suc a))))) suc)))

