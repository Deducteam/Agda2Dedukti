require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Bool as Agda__Builtin__Bool;
constant symbol TYPE__Nat : TYPE;
constant symbol Nat : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ Nat ↪ TYPE__Nat;
constant symbol Nat__zero : El (set (s 0ₙ z)) Nat;
constant symbol Nat__suc : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ n, Nat));



symbol {|_+_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, Nat))));
rule {|_+_|} Nat__zero $m ↪ $m;
rule {|_+_|} (Nat__suc $n) $m ↪ Nat__suc ({|_+_|} $n $m);
 
symbol {|_-_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, Nat))));
rule {|_-_|} $n Nat__zero ↪ $n;
rule {|_-_|} Nat__zero (Nat__suc $m) ↪ Nat__zero;
rule {|_-_|} (Nat__suc $n) (Nat__suc $m) ↪ {|_-_|} $n $m;
 
symbol {|_*_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, Nat))));
rule {|_*_|} Nat__zero $m ↪ Nat__zero;
rule {|_*_|} (Nat__suc $n) $m ↪ {|_+_|} $m ({|_*_|} $n $m);
 
symbol {|_==_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, Agda__Builtin__Bool.Bool))));
rule {|_==_|} Nat__zero Nat__zero ↪ Agda__Builtin__Bool.Bool__true;
rule {|_==_|} (Nat__suc $n) (Nat__suc $m) ↪ {|_==_|} $n $m;
rule {|_==_|} $x0 $x ↪ Agda__Builtin__Bool.Bool__false;
 
symbol {|_<_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ _0, Agda__Builtin__Bool.Bool))));
rule {|_<_|} $x Nat__zero ↪ Agda__Builtin__Bool.Bool__false;
rule {|_<_|} Nat__zero (Nat__suc $n) ↪ Agda__Builtin__Bool.Bool__true;
rule {|_<_|} (Nat__suc $n) (Nat__suc $m) ↪ {|_<_|} $n $m;
 
symbol {|div-helper|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ k, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ m, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ n, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ j, Nat))))))));
rule {|div-helper|} $k $m Nat__zero $j ↪ $k;
rule {|div-helper|} $k $m (Nat__suc $n) Nat__zero ↪ {|div-helper|} (Nat__suc $k) $m $n $m;
rule {|div-helper|} $k $m (Nat__suc $n) (Nat__suc $j) ↪ {|div-helper|} $k $m $n $j;
 
symbol {|mod-helper|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ k, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ m, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ n, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Nat (λ j, Nat))))))));
rule {|mod-helper|} $k $m Nat__zero $j ↪ $k;
rule {|mod-helper|} $k $m (Nat__suc $n) Nat__zero ↪ {|mod-helper|} Nat__zero $m $n $m;
rule {|mod-helper|} $k $m (Nat__suc $n) (Nat__suc $j) ↪ {|mod-helper|} (Nat__suc $k) $m $n $j;
 
