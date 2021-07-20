require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

require tests.paramMod as paramMod;
constant symbol TYPE__B : TYPE;
constant symbol B : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ B ↪ TYPE__B;

symbol fun_inst : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) B (λ _0, B));
rule fun_inst $x ↪ η (s 0ₙ z) B (paramMod.fun B (η (s 0ₙ z) B $x) (η (s 0ₙ z) B $x));
 
