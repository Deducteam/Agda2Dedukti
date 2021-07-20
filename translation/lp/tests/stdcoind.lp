require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
constant symbol TYPE__Thunk : Π {|!ℓ|} : L, Π F : El (set (s (sₙ 0ₙ) ({|!ℓ|} ⊕ z))) (⋄ (set (s 0ₙ ({|!ℓ|} ⊕ z)))), TYPE;
constant symbol Thunk : El setω (∀ (λ {|!ℓ|}, set (s (sₙ 0ₙ) ({|!ℓ|} ⊕ z))) (λ {|!ℓ|}, ⇝ (set (s (sₙ 0ₙ) ({|!ℓ|} ⊕ z))) (set (s (sₙ 0ₙ) ({|!ℓ|} ⊕ z))) (⋄ (set (s 0ₙ ({|!ℓ|} ⊕ z)))) (λ F, (⋄ (set (s 0ₙ ({|!ℓ|} ⊕ z)))))));
rule El _ (Thunk ${|!ℓ|} $F) ↪ TYPE__Thunk ${|!ℓ|} $F;
constant symbol {|!Thunk'constructor|} : El setω (∀ (λ {|!ℓ|}, set (s (sₙ 0ₙ) ({|!ℓ|} ⊕ z))) (λ {|!ℓ|}, ⇝ (set (s (sₙ 0ₙ) ({|!ℓ|} ⊕ z))) (set (s 0ₙ ({|!ℓ|} ⊕ z))) (⋄ (set (s 0ₙ ({|!ℓ|} ⊕ z)))) (λ F, (⇝ (set (s 0ₙ ({|!ℓ|} ⊕ z))) (set (s 0ₙ ({|!ℓ|} ⊕ z))) F (λ force, (Thunk {|!ℓ|} F))))));
symbol Thunk__force : El setω (∀ (λ {|!ℓ|}, set (s (sₙ 0ₙ) ({|!ℓ|} ⊕ z))) (λ {|!ℓ|}, ⇝ (set (s (sₙ 0ₙ) ({|!ℓ|} ⊕ z))) (set (s 0ₙ ({|!ℓ|} ⊕ z))) (⋄ (set (s 0ₙ ({|!ℓ|} ⊕ z)))) (λ F, (⇝proj (set (s 0ₙ ({|!ℓ|} ⊕ z))) (set (s 0ₙ ({|!ℓ|} ⊕ z))) (Thunk {|!ℓ|} F) (λ r, F)))));

rule η _ (Thunk ${|!ℓ|} $F) $y ↪ $y;
 
rule Thunk__force ${|!ℓ|} $F ({|!Thunk'constructor|} _ _ $force) ↪ η (s 0ₙ (${|!ℓ|} ⊕ z)) $F $force;
 
constant symbol TYPE__Colist : Π a : L, Π A : El (set (s (sₙ 0ₙ) (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))), TYPE;
constant symbol Colist : El setω (∀ (λ a, set (s (sₙ 0ₙ) (a ⊕ z))) (λ a, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set (s (sₙ 0ₙ) (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⋄ (set (s 0ₙ (a ⊕ z)))))));
rule El _ (Colist $a $A) ↪ TYPE__Colist $a $A;
constant symbol {|!Colist__[]|} : El setω (∀ (λ a, set (s (sₙ 0ₙ) (a ⊕ z))) (λ a, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set (s 0ₙ (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (Colist a A))));
constant symbol {|!Colist___∷_|} : El setω (∀ (λ a, set (s (sₙ 0ₙ) (a ⊕ z))) (λ a, ⇝ (set (s (sₙ 0ₙ) (a ⊕ z))) (set (s 0ₙ (a ⊕ z))) (⋄ (set (s 0ₙ (a ⊕ z)))) (λ A, (⇝ (set (s 0ₙ (a ⊕ z))) (set (s 0ₙ (a ⊕ z))) A (λ _0, (⇝ (set (s 0ₙ (a ⊕ z))) (set (s 0ₙ (a ⊕ z))) (Thunk a (Colist a A)) (λ _0, (Colist a A))))))));
rule η _ (Colist _ _) ({|!Colist__[]|} $a $A) ↪ {|!Colist__[]|} $a $A;
rule η _ (Colist _ _) ({|!Colist___∷_|} $a $A $x0 $x) ↪ {|!Colist___∷_|} $a $A (η (s 0ₙ ($a ⊕ z)) $A $x0) $x;
 


symbol zeros : El (set (s 0ₙ z)) (Colist (s 0ₙ z) Agda__Builtin__Nat.Nat);
symbol {|!'extendedlambda0|} : El (set (s 0ₙ z)) (Thunk (s 0ₙ z) (Colist (s 0ₙ z) Agda__Builtin__Nat.Nat));
rule zeros ↪ η (s 0ₙ z) (Colist (s 0ₙ z) Agda__Builtin__Nat.Nat) ({|!Colist___∷_|} (s 0ₙ z) Agda__Builtin__Nat.Nat (η (s 0ₙ ((s 0ₙ z) ⊕ z)) Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat__zero) {|!'extendedlambda0|});
 
rule Thunk__force _ _ {|!'extendedlambda0|} ↪ η (s 0ₙ z) (Colist (s 0ₙ z) Agda__Builtin__Nat.Nat) zeros;
 
symbol {|!Thunk^R|} : El setω (∀ (λ f, setω) (λ f, ∀ (λ g, setω) (λ g, ∀ (λ r, set ((s 0ₙ z) ⊕ ((s (sₙ 0ₙ) (f ⊕ z)) ⊕ ((s (sₙ 0ₙ) (g ⊕ z)) ⊕ (s (sₙ 0ₙ) (r ⊕ z)))))) (λ r, ⇝ (set (s (sₙ 0ₙ) (f ⊕ z))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (f ⊕ z)) ⊕ ((s (sₙ 0ₙ) (g ⊕ z)) ⊕ (s (sₙ 0ₙ) (r ⊕ z)))))) (⋄ (set (s 0ₙ (f ⊕ z)))) (λ F, (⇝ (set (s (sₙ 0ₙ) (g ⊕ z))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (f ⊕ z)) ⊕ ((s 0ₙ (g ⊕ z)) ⊕ (s (sₙ 0ₙ) (r ⊕ z)))))) (⋄ (set (s 0ₙ (g ⊕ z)))) (λ G, (⇝ (set ((s 0ₙ z) ⊕ ((s 0ₙ (f ⊕ z)) ⊕ ((s 0ₙ (g ⊕ z)) ⊕ (s (sₙ 0ₙ) (r ⊕ z)))))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (f ⊕ z)) ⊕ ((s 0ₙ (g ⊕ z)) ⊕ (s (sₙ 0ₙ) (r ⊕ z)))))) (⇝ (set (s 0ₙ (f ⊕ z))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (g ⊕ z)) ⊕ (s (sₙ 0ₙ) (r ⊕ z))))) F (λ _0, (⇝ (set (s 0ₙ (g ⊕ z))) (set (s (sₙ 0ₙ) (r ⊕ z))) G (λ _0, (⋄ (set (s 0ₙ (r ⊕ z)))))))) (λ R, (⇝ (set (s 0ₙ (f ⊕ z))) (set ((s 0ₙ z) ⊕ ((s 0ₙ (g ⊕ z)) ⊕ (s (sₙ 0ₙ) (r ⊕ z))))) (Thunk f F) (λ tf, (⇝ (set (s 0ₙ (g ⊕ z))) (set (s (sₙ 0ₙ) (r ⊕ z))) (Thunk g G) (λ tg, (⋄ (set (s 0ₙ (r ⊕ z)))))))))))))))));
rule {|!Thunk^R|} $f $g $r $F $G $R $tf $tg ↪ Thunk $r ($R (η (s 0ₙ ($f ⊕ z)) $F (Thunk__force $f $F $tf)) (η (s 0ₙ ($g ⊕ z)) $G (Thunk__force $g $G $tg)));
 
