module rose_tree_aux where

data rose_tree : Set
data rose_tree_l : Set

data rose_tree where
 Nd : rose_tree_l → rose_tree

data rose_tree_l where
 Nil : rose_tree_l
 Cons : rose_tree → rose_tree_l → rose_tree_l

map : (rose_tree → rose_tree_l) → rose_tree → rose_tree
aux : (rose_tree → rose_tree_l) → rose_tree_l → rose_tree_l

map f (Nd l) = Nd (aux f l)
aux f Nil = f (Nd Nil)
aux f (Cons a tl) = Cons (map f a) (aux f tl)