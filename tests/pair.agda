module pair where

data X : Set where
 arr : X → X → X

data and : Set → Set → Set where
 pair : (A B : Set) → and A B

subtype : X → X → Set
subtype (arr a b) (arr a' b') = and (subtype a' a) (subtype b b')
