require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

constant symbol {|!TYPE__⊥|} : TYPE;
constant symbol {|!⊥|} : El (set (s (sₙ 0ₙ) z)) (⋄ (prop (s 0ₙ z)));
rule El _ {|!⊥|} ↪ {|!TYPE__⊥|};

constant symbol {|!TYPE__⊤|} : TYPE;
constant symbol {|!⊤|} : El (set (s (sₙ 0ₙ) z)) (⋄ (prop (s 0ₙ z)));
rule El _ {|!⊤|} ↪ {|!TYPE__⊤|};
constant symbol tt : El (prop (s 0ₙ z)) {|!⊤|};


