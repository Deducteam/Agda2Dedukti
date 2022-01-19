open import Agda.Primitive
open import Agda.Builtin.Equality
comp : ((i : Level) → Set i → Set i) → ((i : Level) → Set i) → (i : Level) → Set i
comp f a i = (f i) (a i)

data Cont : Setω where
  box : (i : Level) → (A : Set i) → ((x y : A) → x ≡ y) → Cont

--getLvl : Cont → Level
--getLvl (box i A p) = i

test : Setω
test = (i j : Level) → (A : Set i) → (B : Set j) → A → B → Set (i ⊔ j)

data TTest (A : Set) : Setω where
  bbox : A → TTest A

data HetEq : (i j : Level) → (A : Set i) → (B : Set j) → A → B → Set where
  hetRefl : (i : Level) → (A : Set i) → (a : A) → HetEq i i A A a a

het-sym : (i j : Level) → (A : Set i) → (B : Set j) → (a : A) → (b : B) → HetEq i j A B a b → HetEq j i B A b a
het-sym i _ A _ a _ (hetRefl i A a) = hetRefl i A a

het-cong : (i j : Level) → (A : Set i) → (B : Set j) → (a : A) → (b : B) → HetEq i j A B a b 
                         → (g : (i : Level) → Set i → Set i) → (f : (i : Level) → (X : Set i) → X → g i X)
                         → HetEq i j (g i A) (g j B) (f i A a) (f j B b)
het-cong i _ A _ a _ (hetRefl _ _ _) g f = hetRefl i (g i A) (f i A a)

-- does not work... why?
--het-transport : (i j : Level) → (A : Set i) → (B : Set j) → HetEq _ _ (Set i) (Set j) A B → A → B
--het-transport i' _ A' _ (hetRefl .i' _ _) x = x
