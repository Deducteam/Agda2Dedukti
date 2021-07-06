require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

constant symbol TYPE__false : TYPE;
constant symbol false : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ false ↪ TYPE__false;

symbol fimp : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) false (λ _0, A))));

constant symbol TYPE__exists : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π P : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z))))), TYPE;
constant symbol exists : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z))))) (λ P, (⋄ (set (s 0ₙ z)))))));
rule El _ (exists $A $P) ↪ TYPE__exists $A $P;
constant symbol exists__exintro : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) A (λ _0, (⋄ (set (s 0ₙ z))))) (λ P, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (P a) (λ p, (exists A P)))))))));


constant symbol TYPE__or : Π _0 : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π _0 : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol or : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ _0, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ _0, (⋄ (set (s 0ₙ z)))))));
rule El _ (or $x0 $x) ↪ TYPE__or $x0 $x;
constant symbol or__orl : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, (or A B)))))));
constant symbol or__orr : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) B (λ b, (or A B)))))));



constant symbol TYPE__and : Π _0 : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π _0 : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol and : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ _0, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ _0, (⋄ (set (s 0ₙ z)))))));
rule El _ (and $x0 $x) ↪ TYPE__and $x0 $x;
constant symbol and__inand : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) B (λ b, (and A B)))))))));


constant symbol TYPE__N : TYPE;
constant symbol N : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ N ↪ TYPE__N;
constant symbol N__zero : El (set (s 0ₙ z)) N;
constant symbol N__suc : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N));



constant symbol TYPE__Neq : Π _0 : El (set (s 0ₙ z)) N, Π _0 : El (set (s 0ₙ z)) N, TYPE;
constant symbol Neq : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) N (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) N (λ _0, (⋄ (set (s 0ₙ z)))))));
rule El _ (Neq $x0 $x) ↪ TYPE__Neq $x0 $x;
constant symbol Neq__refl : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (Neq x x)));


symbol cong : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Neq x y) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N)) (λ f, (Neq (f x) (f y))))))))));
rule cong $x _ (Neq__refl _) $f ↪ Neq__refl ($f $x);
 
symbol sym : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Neq x y) (λ _0, (Neq y x)))))));
rule sym $x _ (Neq__refl _) ↪ Neq__refl $x;
 
symbol trs : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ {|!z|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Neq x y) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Neq y {|!z|}) (λ _0, (Neq x {|!z|})))))))))));
rule trs $x _ _ (Neq__refl _) (Neq__refl _) ↪ Neq__refl $x;
 
symbol suc0 : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Neq (N__suc x) N__zero) (λ _0, false))));

symbol sum : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N))));
rule sum N__zero $x ↪ $x;
rule sum (N__suc $x0) $x ↪ N__suc (sum $x0 $x);
 
symbol sum0 : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (Neq x (sum x N__zero))));
rule sum0 N__zero ↪ Neq__refl N__zero;
rule sum0 (N__suc $x) ↪ cong $x (sum $x N__zero) (sum0 $x) N__suc;
 
symbol sumassos : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ {|!z|}, (Neq (sum x (sum y {|!z|})) (sum (sum x y) {|!z|}))))))));
symbol {|!with-138|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ {|!z|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Neq (sum x (sum y {|!z|})) (sum (sum x y) {|!z|})) (λ w, (Neq (N__suc (sum x (sum y {|!z|}))) (N__suc (sum (sum x y) {|!z|})))))))))));
rule sumassos N__zero $y ${|!z|} ↪ Neq__refl (sum $y ${|!z|});
rule sumassos (N__suc $x) $y ${|!z|} ↪ {|!with-138|} $x $y ${|!z|} (sumassos $x $y ${|!z|});
 
rule {|!with-138|} $x $y ${|!z|} $w ↪ cong (sum $x (sum $y ${|!z|})) (sum (sum $x $y) ${|!z|}) $w N__suc;
 
symbol sumcom : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (Neq (sum x y) (sum y x))))));
rule sumcom N__zero N__zero ↪ Neq__refl N__zero;
rule sumcom N__zero (N__suc $y) ↪ sum0 (N__suc $y);
rule sumcom (N__suc $x) N__zero ↪ sym (sum N__zero (N__suc $x)) (sum (N__suc $x) N__zero) (sum0 (N__suc $x));
rule sumcom (N__suc $x) (N__suc $y) ↪ cong (sum $x (N__suc $y)) (sum $y (N__suc $x)) (trs (sum $x (N__suc $y)) (sum (N__suc $y) $x) (sum $y (N__suc $x)) (sumcom $x (N__suc $y)) (trs (sum (N__suc $y) $x) (N__suc (sum $x $y)) (sum $y (N__suc $x)) (cong (sum $y $x) (sum $x $y) (sumcom $y $x) N__suc) (sumcom (N__suc $x) $y))) N__suc;
 
symbol mult : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ _0, N))));
rule mult N__zero $x ↪ N__zero;
rule mult (N__suc $x0) $x ↪ sum $x (mult $x0 $x);
 
symbol mult0 : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (Neq N__zero (mult x N__zero))));
rule mult0 N__zero ↪ Neq__refl N__zero;
rule mult0 (N__suc $x) ↪ mult0 $x;
 
symbol multcom : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (Neq (mult x y) (mult y x))))));
rule multcom N__zero N__zero ↪ Neq__refl N__zero;
rule multcom N__zero (N__suc $y) ↪ mult0 (N__suc $y);
rule multcom (N__suc $x) N__zero ↪ sym (mult N__zero (N__suc $x)) (mult (N__suc $x) N__zero) (mult0 (N__suc $x));
rule multcom (N__suc $x) (N__suc $y) ↪ cong (sum $y (mult $x (N__suc $y))) (sum $x (mult $y (N__suc $x))) (trs (sum $y (mult $x (N__suc $y))) (sum $y (mult (N__suc $y) $x)) (sum $x (mult $y (N__suc $x))) (cong (mult $x (N__suc $y)) (mult (N__suc $y) $x) (multcom $x (N__suc $y)) (sum $y)) (trs (sum $y (mult (N__suc $y) $x)) (sum $x (sum $y (mult $x $y))) (sum $x (mult $y (N__suc $x))) (trs (sum $y (mult (N__suc $y) $x)) (sum (sum $y $x) (mult $y $x)) (sum $x (sum $y (mult $x $y))) (sumassos $y $x (mult $y $x)) (trs (sum (sum $y $x) (mult $y $x)) (sum (sum $x $y) (mult $x $y)) (sum $x (sum $y (mult $x $y))) (trs (sum (sum $y $x) (mult $y $x)) (sum (sum $x $y) (mult $y $x)) (sum (sum $x $y) (mult $x $y)) (cong (sum $y $x) (sum $x $y) (sumcom $y $x) (λ a, sum a (mult $y $x))) (cong (mult $y $x) (mult $x $y) (multcom $y $x) (sum (sum $x $y)))) (sym (sum $x (sum $y (mult $x $y))) (sum (sum $x $y) (mult $x $y)) (sumassos $x $y (mult $x $y))))) (cong (mult (N__suc $x) $y) (mult $y (N__suc $x)) (multcom (N__suc $x) $y) (sum $x)))) N__suc;
 
constant symbol TYPE__Nleq : Π _0 : El (set (s 0ₙ z)) N, Π _0 : El (set (s 0ₙ z)) N, TYPE;
constant symbol Nleq : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) N (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) N (λ _0, (⋄ (set (s 0ₙ z)))))));
rule El _ (Nleq $x0 $x) ↪ TYPE__Nleq $x0 $x;
constant symbol Nleq__0leq : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (Nleq N__zero x)));
constant symbol Nleq__Sleq : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq x y) (λ _0, (Nleq (N__suc x) (N__suc y))))))));



symbol exm : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (or (Nleq x y) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq x y) (λ _0, false)))))));
symbol {|!with-226|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (or (Nleq x y) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq x y) (λ _0, false))) (λ w, (or (Nleq (N__suc x) (N__suc y)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq (N__suc x) (N__suc y)) (λ _0, false)))))))));
symbol {|!'extendedlambda0|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq x y) (λ _0, false)) (λ b, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq (N__suc x) (N__suc y)) (λ _0, false))))))));
symbol {|!'absurdlambda-2941|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq (N__suc x) N__zero) (λ _0, false))));
rule exm N__zero $y ↪ or__orl (Nleq N__zero $y) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq N__zero $y) (λ _0, false)) (Nleq__0leq $y);
rule exm (N__suc $x) N__zero ↪ or__orr (Nleq (N__suc $x) N__zero) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq (N__suc $x) N__zero) (λ _0, false)) ({|!'absurdlambda-2941|} $x);
rule exm (N__suc $x) (N__suc $y) ↪ {|!with-226|} $x $y (exm $x $y);
 
rule {|!with-226|} $x $y (or__orl _ _ $a) ↪ or__orl (Nleq (N__suc $x) (N__suc $y)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq (N__suc $x) (N__suc $y)) (λ _0, false)) (Nleq__Sleq $x $y $a);
rule {|!with-226|} $x $y (or__orr _ _ $b) ↪ or__orr (Nleq (N__suc $x) (N__suc $y)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq (N__suc $x) (N__suc $y)) (λ _0, false)) ({|!'extendedlambda0|} $x $y $b);
 
rule {|!'extendedlambda0|} $x0 $y $b (Nleq__Sleq _ _ $x) ↪ $b $x;
 

symbol strictornot : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq x y) (λ _0, (or (Neq x y) (Nleq (N__suc x) y))))))));
symbol {|!with-266|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq x y) (λ p, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (or (Neq x y) (Nleq (N__suc x) y)) (λ w, (or (Neq (N__suc x) (N__suc y)) (Nleq (N__suc (N__suc x)) (N__suc y)))))))))));
rule strictornot N__zero N__zero $x ↪ or__orl (Neq N__zero N__zero) (Nleq (N__suc N__zero) N__zero) (Neq__refl N__zero);
rule strictornot N__zero (N__suc $y) $x ↪ or__orr (Neq N__zero (N__suc $y)) (Nleq (N__suc N__zero) (N__suc $y)) (Nleq__Sleq N__zero $y (Nleq__0leq $y));
rule strictornot (N__suc $x0) (N__suc $y) (Nleq__Sleq _ _ $x) ↪ {|!with-266|} $x0 $y $x (strictornot $x0 $y $x);
 
rule {|!with-266|} $x _ $p (or__orl _ _ (Neq__refl _)) ↪ or__orl (Neq (N__suc $x) (N__suc $x)) (Nleq (N__suc (N__suc $x)) (N__suc $x)) (Neq__refl (N__suc $x));
rule {|!with-266|} $x $y $p (or__orr _ _ $b) ↪ or__orr (Neq (N__suc $x) (N__suc $y)) (Nleq (N__suc (N__suc $x)) (N__suc $y)) (Nleq__Sleq (N__suc $x) $y $b);
 
symbol minus : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq y x) (λ p, (exists N (λ a, Neq x (sum y a)))))))));
symbol {|!with-304|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq y x) (λ p, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (exists N (λ a, Neq x (sum y a))) (λ w, (exists N (λ a, Neq (N__suc x) (N__suc (sum y a))))))))))));
rule minus N__zero N__zero $p ↪ exists__exintro N (λ a, Neq N__zero (sum N__zero a)) N__zero (Neq__refl N__zero);
rule minus (N__suc $x) N__zero $p ↪ exists__exintro N (λ a, Neq (N__suc $x) (sum N__zero a)) (N__suc $x) (Neq__refl (N__suc $x));
rule minus (N__suc $x) (N__suc $y) (Nleq__Sleq _ _ $p) ↪ {|!with-304|} $x $y $p (minus $x $y $p);
 
rule {|!with-304|} $x $y $p0 (exists__exintro _ _ $a $p) ↪ exists__exintro N (λ a0, Neq (N__suc $x) (N__suc (sum $y a0))) $a (cong $x (sum $y $a) $p N__suc);
 
symbol euclid : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Neq y N__zero) (λ _0, false)) (λ p, (exists N (λ p, exists N (λ r, and (Nleq (N__suc r) y) (Neq x (sum (mult y p) r)))))))))));
symbol {|!with-344|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Neq y N__zero) (λ _0, false)) (λ p, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (exists N (λ p0, exists N (λ r, and (Nleq (N__suc r) y) (Neq x (sum (mult y p0) r))))) (λ w, (exists N (λ p0, exists N (λ r, and (Nleq (N__suc r) y) (Neq (N__suc x) (sum (mult y p0) r)))))))))))));
symbol {|!with-362|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ a2, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Nleq (N__suc a2) y) (λ b1, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (or (Neq (N__suc a2) y) (Nleq (N__suc (N__suc a2)) y)) (λ w, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Neq y N__zero) (λ _0, false)) (λ p, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) N (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Neq x (sum (mult y a) a2)) (λ b2, (exists N (λ p0, exists N (λ r, and (Nleq (N__suc r) y) (Neq (N__suc x) (sum (mult y p0) r)))))))))))))))))))));
rule euclid $x N__zero $p ↪ fimp (exists N (λ p0, exists N (λ r, and (Nleq (N__suc r) N__zero) (Neq $x (sum (mult N__zero p0) r))))) ($p (Neq__refl N__zero));
rule euclid N__zero (N__suc $y) $p ↪ exists__exintro N (λ p0, exists N (λ r, and (Nleq (N__suc r) (N__suc $y)) (Neq N__zero (sum (mult (N__suc $y) p0) r)))) N__zero (exists__exintro N (λ r, and (Nleq (N__suc r) (N__suc $y)) (Neq N__zero (sum (mult (N__suc $y) N__zero) r))) N__zero (and__inand (Nleq (N__suc N__zero) (N__suc $y)) (Neq N__zero (sum (mult (N__suc $y) N__zero) N__zero)) (Nleq__Sleq N__zero $y (Nleq__0leq $y)) (trs N__zero (mult $y N__zero) (sum (mult (N__suc $y) N__zero) N__zero) (mult0 $y) (sum0 (mult $y N__zero)))));
rule euclid (N__suc $x) (N__suc $y) $p ↪ {|!with-344|} $x (N__suc $y) $p (euclid $x (N__suc $y) $p);
 
rule {|!with-344|} $x $y $p (exists__exintro _ _ $a1 (exists__exintro _ _ $a0 (and__inand _ _ $a $b))) ↪ {|!with-362|} $y $a0 $a (strictornot (N__suc $a0) $y $a) $x $p $a1 $b;
 
rule {|!with-362|} (N__suc $y) _ $b1 (or__orl _ _ (Neq__refl _)) _ $p $a (Neq__refl _) ↪ exists__exintro N (λ p0, exists N (λ r, and (Nleq (N__suc r) (N__suc $y)) (Neq (N__suc (sum (mult (N__suc $y) $a) $y)) (sum (mult (N__suc $y) p0) r)))) (N__suc $a) (exists__exintro N (λ r, and (Nleq (N__suc r) (N__suc $y)) (Neq (N__suc (sum (mult (N__suc $y) $a) $y)) (sum (mult (N__suc $y) (N__suc $a)) r))) N__zero (and__inand (Nleq (N__suc N__zero) (N__suc $y)) (Neq (N__suc (sum (mult (N__suc $y) $a) $y)) (sum (mult (N__suc $y) (N__suc $a)) N__zero)) (Nleq__Sleq N__zero $y (Nleq__0leq $y)) (cong (sum (sum $a (mult $y $a)) $y) (sum (sum $a (mult $y (N__suc $a))) N__zero) (trs (sum (sum $a (mult $y $a)) $y) (sum $a (mult $y (N__suc $a))) (sum (sum $a (mult $y (N__suc $a))) N__zero) (trs (sum (sum $a (mult $y $a)) $y) (sum $a (sum (mult $y $a) $y)) (sum $a (mult $y (N__suc $a))) (sym (sum $a (sum (mult $y $a) $y)) (sum (sum $a (mult $y $a)) $y) (sumassos $a (mult $y $a) $y)) (cong (sum (mult $y $a) $y) (mult $y (N__suc $a)) (trs (sum (mult $y $a) $y) (sum $y (mult $y $a)) (mult $y (N__suc $a)) (sumcom (mult $y $a) $y) (trs (sum $y (mult $y $a)) (sum $y (mult $a $y)) (mult $y (N__suc $a)) (cong (mult $y $a) (mult $a $y) (multcom $y $a) (sum $y)) (multcom (N__suc $a) $y))) (sum $a))) (sum0 (sum $a (mult $y (N__suc $a))))) N__suc)));
rule {|!with-362|} $y $a2 $b1 (or__orr _ _ $b) $x $p $a $b2 ↪ exists__exintro N (λ p0, exists N (λ r, and (Nleq (N__suc r) $y) (Neq (N__suc $x) (sum (mult $y p0) r)))) $a (exists__exintro N (λ r, and (Nleq (N__suc r) $y) (Neq (N__suc $x) (sum (mult $y $a) r))) (N__suc $a2) (and__inand (Nleq (N__suc (N__suc $a2)) $y) (Neq (N__suc $x) (sum (mult $y $a) (N__suc $a2))) $b (trs (N__suc $x) (N__suc (sum $a2 (mult $y $a))) (sum (mult $y $a) (N__suc $a2)) (cong $x (sum $a2 (mult $y $a)) (trs $x (sum (mult $y $a) $a2) (sum $a2 (mult $y $a)) $b2 (sumcom (mult $y $a) $a2)) N__suc) (sumcom (N__suc $a2) (mult $y $a)))));
 
