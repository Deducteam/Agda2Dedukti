record Σ (A : Set ) (B : A → Set) : Set where
  field
    fst : A
    snd : B fst

