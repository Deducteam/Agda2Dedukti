{-# OPTIONS --guardedness #-}
record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A

open Stream
