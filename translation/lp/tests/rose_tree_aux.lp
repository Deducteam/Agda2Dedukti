require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

constant symbol TYPE__rose_tree : TYPE;
constant symbol rose_tree : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ rose_tree ↪ TYPE__rose_tree;
constant symbol TYPE__rose_tree_l : TYPE;
constant symbol rose_tree_l : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ rose_tree_l ↪ TYPE__rose_tree_l;
constant symbol rose_tree__Nd : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) rose_tree_l (λ _0, rose_tree));
constant symbol rose_tree_l__Nil : El (set (s 0ₙ z)) rose_tree_l;
constant symbol rose_tree_l__Cons : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) rose_tree (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) rose_tree_l (λ _0, rose_tree_l))));





symbol map : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) rose_tree (λ _0, rose_tree_l)) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) rose_tree (λ _0, rose_tree))));
symbol aux : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) rose_tree (λ _0, rose_tree_l)) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) rose_tree_l (λ _0, rose_tree_l))));
rule map $x0 (rose_tree__Nd $x) ↪ rose_tree__Nd (aux $x0 $x);
 
rule aux $x rose_tree_l__Nil ↪ $x (rose_tree__Nd rose_tree_l__Nil);
rule aux $x1 (rose_tree_l__Cons $x0 $x) ↪ rose_tree_l__Cons (map $x1 $x0) (aux $x1 $x);
 
