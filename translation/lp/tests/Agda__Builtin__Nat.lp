require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Bool as Agda__Builtin__Bool;
constant symbol TYPE__Nat : TYPE;
constant symbol Nat : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ Nat ↪ TYPE__Nat;
constant symbol Nat__zero : El (set (s 0ₙ z)) Nat;
constant symbol Nat__suc : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ n, Nat));
rule η _ Nat Nat__zero ↪ Nat__zero;
rule η _ Nat (Nat__suc $n) ↪ Nat__suc (η (s 0ₙ z) Nat $n);
 


symbol {|!_+_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, Nat))));
rule {|!_+_|} Nat__zero $m ↪ η (s 0ₙ z) Nat $m;
rule {|!_+_|} (Nat__suc $n) $m ↪ η (s 0ₙ z) Nat (Nat__suc (η (s 0ₙ z) Nat ({|!_+_|} (η (s 0ₙ z) Nat $n) (η (s 0ₙ z) Nat $m))));
 
symbol {|!_-_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, Nat))));
rule {|!_-_|} $n Nat__zero ↪ η (s 0ₙ z) Nat $n;
rule {|!_-_|} Nat__zero (Nat__suc $m) ↪ η (s 0ₙ z) Nat Nat__zero;
rule {|!_-_|} (Nat__suc $n) (Nat__suc $m) ↪ η (s 0ₙ z) Nat ({|!_-_|} (η (s 0ₙ z) Nat $n) (η (s 0ₙ z) Nat $m));
 
symbol {|!_*_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, Nat))));
rule {|!_*_|} Nat__zero $m ↪ η (s 0ₙ z) Nat Nat__zero;
rule {|!_*_|} (Nat__suc $n) $m ↪ η (s 0ₙ z) Nat ({|!_+_|} (η (s 0ₙ z) Nat $m) (η (s 0ₙ z) Nat ({|!_*_|} (η (s 0ₙ z) Nat $n) (η (s 0ₙ z) Nat $m))));
 
symbol {|!_==_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, Agda__Builtin__Bool.Bool))));
rule {|!_==_|} Nat__zero Nat__zero ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true;
rule {|!_==_|} (Nat__suc $n) (Nat__suc $m) ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_==_|} (η (s 0ₙ z) Nat $n) (η (s 0ₙ z) Nat $m));
rule {|!_==_|} $x0 $x ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false;
 
symbol {|!_<_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, Agda__Builtin__Bool.Bool))));
rule {|!_<_|} $x Nat__zero ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__false;
rule {|!_<_|} Nat__zero (Nat__suc $n) ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool Agda__Builtin__Bool.Bool__true;
rule {|!_<_|} (Nat__suc $n) (Nat__suc $m) ↪ η (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_<_|} (η (s 0ₙ z) Nat $n) (η (s 0ₙ z) Nat $m));
 
symbol {|!div-helper|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ k, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ m, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ n, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ j, Nat))))))));
rule {|!div-helper|} $k $m Nat__zero $j ↪ η (s 0ₙ z) Nat $k;
rule {|!div-helper|} $k $m (Nat__suc $n) Nat__zero ↪ η (s 0ₙ z) Nat ({|!div-helper|} (η (s 0ₙ z) Nat (Nat__suc (η (s 0ₙ z) Nat $k))) (η (s 0ₙ z) Nat $m) (η (s 0ₙ z) Nat $n) (η (s 0ₙ z) Nat $m));
rule {|!div-helper|} $k $m (Nat__suc $n) (Nat__suc $j) ↪ η (s 0ₙ z) Nat ({|!div-helper|} (η (s 0ₙ z) Nat $k) (η (s 0ₙ z) Nat $m) (η (s 0ₙ z) Nat $n) (η (s 0ₙ z) Nat $j));
 
symbol {|!mod-helper|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ k, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ m, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ n, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ j, Nat))))))));
rule {|!mod-helper|} $k $m Nat__zero $j ↪ η (s 0ₙ z) Nat $k;
rule {|!mod-helper|} $k $m (Nat__suc $n) Nat__zero ↪ η (s 0ₙ z) Nat ({|!mod-helper|} (η (s 0ₙ z) Nat Nat__zero) (η (s 0ₙ z) Nat $m) (η (s 0ₙ z) Nat $n) (η (s 0ₙ z) Nat $m));
rule {|!mod-helper|} $k $m (Nat__suc $n) (Nat__suc $j) ↪ η (s 0ₙ z) Nat ({|!mod-helper|} (η (s 0ₙ z) Nat (Nat__suc (η (s 0ₙ z) Nat $k))) (η (s 0ₙ z) Nat $m) (η (s 0ₙ z) Nat $n) (η (s 0ₙ z) Nat $j));
 
