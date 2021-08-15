# Agda2Dedukti : A translator from Agda to Dedukti and Lambdapi

This is a translator from the Agda proof assistant to an encoding of its logic in the lambda-pi calculus modulo rewriting, implemented in Dedukti and Lambdapi.

## How to use

This translator is written as an Agda backend, and thus needs Agda to be present. It runs almost directly with the Agda master branch, however it also needs the changes present in [https://github.com/agda/agda/pull/3909](https://github.com/agda/agda/pull/3909), which should be merged into the master soon. More precisely, this code was last checked to work on commit 4d972a3c6f7d75d42dc7e7eae9626d925c2c3f69 with the changes on [https://github.com/agda/agda/pull/3909](https://github.com/agda/agda/pull/3909).

### Modes

The translator has two modes which are used to specify the target of the translator.

- Lambdapi mode : By default, the translator produces a Dedukti file, and the user needs to use the theory files in `theory/dk` to check the file. However, by using the `--lp` flag, the translator enters Lambdapi mode, and produces a Lambdapi file which needs to be checked with the theory files in `theory/lp`.

- Eta-conversion mode : Agda is a proof assistant which has eta-equality in its conversion system. This is not always needed when translating proofs, by if it should be the case, the user can use the fla `--eta`, which produces a files that should be checked using the theory files with eta conversion. In this case, in the directory `theory/dk` (or `theory/lp/AgdaTheory`) we should use the files in the folder `eta`. Note that when using eta conversion the size of the files becomes much bigger, and some files that can be checked with Dedukti won't work with Lambdapi.

Explicitly, given an Agda file, and assuming that Agda2Dedukti has been built with cabal, we use the following commands to translate it to Dedukti or Lambdapi, with or without eta-conversion.
```
dist/build/Agda2Dedukti/Agda2Dedukti --dk file.agda		(Dedukti, no eta)
dist/build/Agda2Dedukti/Agda2Dedukti --dk --eta file.agda	(Dedukti, with eta)
dist/build/Agda2Dedukti/Agda2Dedukti --dk --lp file.agda	(Lambdapi, no eta)
dist/build/Agda2Dedukti/Agda2Dedukti --dk --lp --eta file.agda	(Lambdapi, with eta)
```

Obs .: If we are translating a file which uses Agda.Primitive into Lambdapi, then the translator will produce a file `Agda__Primitive.lp` which will not work. To get a working translator of Agda.Primitive, one should copy the file `Agda__Primitive-noEta.lp` (or `Agda__Primitive-eta.lp`) in `translation/lp` into the working directory, and rename it into `Agda__Primitive.lp`.

### Typechecking

Assuming that the working directory is `translation/dk/tests`, then we can typecheck a Dedukti file (not using eta-conversion) with the following command. We should use the directory `theory/dk/eta/` if using eta-conversion.
```
dkcheck -I ../../../theory/dk/noEta/ file.dk
```

In order to typecheck a Lambdapi file, one should first run `make install` on `theory/lp/AgdaTheory`. Then it suffices to run the following command.
```
lambdapi check file.lp
```

## Running tests

The directory `tests` contains test files which can be used to test the translator, using the following commands.
```
make test-dk-noEta
make test-dk-eta
make test-lp-noEta
make test-lp-eta
```
The mode Dedukti with eta is the one which typechecks most files, whereas Lambdapi with eta typechecks the least. For each mode, expect the following number of files to typecheck:

- Dedukti with eta : 53 / 57
- Dedukti without eta : 50  / 57
- Lambdapi with eta : 40 / 57
- Lambdapi whithout eta : 50 / 57

Introducing a new feature into the translation should help to typecheck more files. However, in the case of Lambdapi, when introducing eta we see that the number of checked files decreases. This is because, when introducing the eta symbol (used in the encoding of eta-conversion), the unification algorithm of Dedukti and Lambdapi is not sufficiently strong to check some of the rewriting rules where it appears. This was avoided in Dedukti with bracket arguments, which is not a completely safe feature and therefore was removed in Lambdapi. It is future work to improve Lambdapi unification algorithm, to enable it to handle such cases. 

## Supported features

A non-exhaustive list of totally or partially supported features :

- Inductive types
- Recursive functions
- Prenex universe polymorphism
- Eta-conversion
- Records
- Copatterns
- Musical coinduction and copattern coinduction

TODO :

- Sized types
- Second hierarchy Set\omega_0 : Set\omega_1 : ...
- Correct errors to use with the standard library
- Rewrite rules

Dream feature : translate Agda function definitions with clauses into definitions only using the elimination principle of inductive types

## Developers and references

The developpement of this translator was started by Guillaume Genestier and is  done today by Thiago Felicissimo, both with the help of Jesper Cockx. The three main references about this translator are the following.

- G. Genestier. Encoding Agda Programs Using Rewriting. In Proceedings of the 5th International Conference on Formal Structures for Computation and Deduction, Leibniz International Proceedings in Informatics 167, 2020.
- T. Felicissimo. Representing Agda and coinduction in the lambda-pi calculus modulo rewriting. Master thesis, 2021. In preparation.
- G. Genestier. Dependently-Typed Termination and Embedding of Extensional Universe-Polymorphic Type Theory using Rewriting. PhD thesis, 2020.
