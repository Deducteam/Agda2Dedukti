module impor where

data B : Set where

open import paramMod B

fun_inst : B -> B
fun_inst x = fun {x} x
