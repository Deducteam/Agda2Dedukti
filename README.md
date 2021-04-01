# Agda2Dedukti

This is the version as Guillaume left it, I only made some small changes so it works with me. 


## Versions that I'm sure that with this code

- Haskell Platform 8.6.5
- Agda: Commit 839f7532f65bc411309c14c771bb972b5c42dd53 of branch dk-translation at https://github.com/Thiagofelis/agda (forked from Guillaume's repo)
- Agda Standard Library: Commit dffb8023 of https://github.com/agda/agda-stdlib
- You will also need the library Unique for Haskell, just doing cabal install Unique should work
- Dedukti: commit 4730853d48615ebff17069f99e4f05fd53ba2cb0 at https://github.com/Deducteam/Dedukti 


## Some changes with respect to the original code

This code was taken from commit 41670ac11a539ac860a82f75a910ac2abfc16546 of branch compile-string of https://github.com/GuillaumeGen/Agda2Dedukti . I made some small changes so it works with me.

- On the source files I had to import prelude hiding the (<>), as it was conflicting with the (<>) defined at the code. Maybe this was not at the prelude on the version Guillaume used.
- Just doing make test would not work as dkcheck would complain that there were no .dko for Agda and univ. Doing `dkcheck -e univ.dk` and then `dkcheck -e Agda.dk` in theory/ solves it.
- On the makefile, `AGDA_STD_DIR` should be set to the source directory of the standard library.

