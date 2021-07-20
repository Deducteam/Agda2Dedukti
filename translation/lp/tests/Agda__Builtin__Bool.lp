require open AgdaTheory.eta.Base;
require open AgdaTheory.Levels;

constant symbol TYPE__Bool : TYPE;
constant symbol Bool : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ Bool ↪ TYPE__Bool;
constant symbol Bool__false : El (set (s 0ₙ z)) Bool;
constant symbol Bool__true : El (set (s 0ₙ z)) Bool;
rule η _ Bool Bool__false ↪ Bool__false;
rule η _ Bool Bool__true ↪ Bool__true;
 


