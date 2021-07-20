require open AgdaTheory.eta.Base;
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
rule η _ rose_tree (rose_tree__Nd $x) ↪ rose_tree__Nd (η (s 0ₙ z) rose_tree_l $x);
 
rule η _ rose_tree_l rose_tree_l__Nil ↪ rose_tree_l__Nil;
rule η _ rose_tree_l (rose_tree_l__Cons $x0 $x) ↪ rose_tree_l__Cons (η (s 0ₙ z) rose_tree $x0) (η (s 0ₙ z) rose_tree_l $x);
 



symbol map : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) rose_tree (λ _0, rose_tree_l)) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) rose_tree (λ _0, rose_tree))));
symbol aux : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) rose_tree (λ _0, rose_tree_l)) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) rose_tree_l (λ _0, rose_tree_l))));
rule map $x0 (rose_tree__Nd $x) ↪ η (s 0ₙ z) rose_tree (rose_tree__Nd (η (s 0ₙ z) rose_tree_l (aux (λ _0, η (s 0ₙ z) rose_tree_l ($x0 (η (s 0ₙ z) rose_tree _0))) (η (s 0ₙ z) rose_tree_l $x))));
 
rule aux $x rose_tree_l__Nil ↪ η (s 0ₙ z) rose_tree_l ($x (η (s 0ₙ z) rose_tree (rose_tree__Nd (η (s 0ₙ z) rose_tree_l rose_tree_l__Nil))));
rule aux $x1 (rose_tree_l__Cons $x0 $x) ↪ η (s 0ₙ z) rose_tree_l (rose_tree_l__Cons (η (s 0ₙ z) rose_tree (map (λ _0, η (s 0ₙ z) rose_tree_l ($x1 (η (s 0ₙ z) rose_tree _0))) (η (s 0ₙ z) rose_tree $x0))) (η (s 0ₙ z) rose_tree_l (aux (λ _0, η (s 0ₙ z) rose_tree_l ($x1 (η (s 0ₙ z) rose_tree _0))) (η (s 0ₙ z) rose_tree_l $x))));
 
