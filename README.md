# Agda2Dedukti : A translator from Agda to Dedukti and Lambdapi

This is a translator from the Agda proof assistant to an encoding of its logic in the lambda-pi calculus modulo rewriting, implemented in Dedukti and Lambdapi.

## How to install

To install Agda2Dedukti you will need:

- `stack >= 2.7.3`
- `ghc >= 8.6.5`

This translator is written as an Agda backend and thus needs it to run. However by running `stack build` Stack should already install an apropriate Agda version in a sandbox and proceed with the build of Agda2Dedukti  --- currently, we are using a branch of Agda in https://github.com/Deducteam/agda/tree/to_dk with a small modification, but in the future it should work with the master branch. 

Once Agda2Dedukti is built, you can already translate Agda files. However, in order to typecheck them you will need to install Dedukti or Lambdapi. The following versions are checked to work: `4cf69db4` for Lambdapi and `c65e7e6` for Dedukti. Then in order to check that everything is working you can do `make test-dk-eta`, which should translate and typecheck most of the test files.

## Modes

The translator has two modes which are used to specify the target of the translator.

- Lambdapi mode : By default, the translator produces a Dedukti file, and the user needs to use the theory files in `theory/dk` to check the file. However, by using the `--lp` flag, the translator enters Lambdapi mode, and produces a Lambdapi file which needs to be checked with the theory files in `theory/lp`.

- Eta-conversion mode : Agda is a proof assistant which has eta-equality in its conversion system. This is not always needed when translating proofs, but if it should be the case, the user can use the flag `--eta`, which produces a files that should be checked using the theory files with eta conversion. In this case, in the directory `theory/dk` (or `theory/lp/AgdaTheory`) we should use the files in the folder `eta`. Note that when using eta conversion the size of the files becomes much bigger, and some files that can be checked with Dedukti may not work with Lambdapi.

Explicitly, given an Agda file, we use the following commands to translate it to Dedukti or Lambdapi, with or without eta-conversion.
```
stack exec -- Agda2Dedukti-exe --dk file.agda               (Dedukti, no eta)
stack exec -- Agda2Dedukti-exe --dk --eta file.agda         (Dedukti, with eta)
stack exec -- Agda2Dedukti-exe --dk --lp  file.agda         (Lambdapi, no eta)
stack exec -- Agda2Dedukti-exe --dk --lp --eta file.agda    (Lambdapi, with eta)
```

If we are translating a file which uses Agda.Primitive into Lambdapi, then the translator will produce a file `Agda__Primitive.lp` which will not work. To get a working translator of Agda.Primitive, one should copy the file `Agda__Primitive-noEta.lp` (or `Agda__Primitive-eta.lp`) from `tests/output/lp` into the working directory, and rename it into `Agda__Primitive.lp`.

## Typechecking

Assuming that the working directory is the root of the project, then we can typecheck a Dedukti file (not using eta-conversion) with the following command. We should use the directory `theory/dk/eta/` if using eta-conversion.
```
dkcheck -I theory/dk/noEta/ file.dk
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
The mode Dedukti with eta is the one which typechecks most files, whereas Lambdapi with eta typechecks the least. For each mode, expect the following number of files to typecheck.

- Dedukti with eta : 50 / 54
- Dedukti without eta : 47 / 54
- Lambdapi with eta : 39 / 54
- Lambdapi whithout eta : 47 / 54

Introducing a new feature into the translation should help to typecheck more files. However, in the case of Lambdapi, when introducing eta we see that the number of checked files decreases. This is because, when introducing the eta symbol (used in the encoding of eta-conversion), the algorithm used to verify subject reduction of rewrite rules in Lambdapi and Dedukti is currently not able to check that some of the generated rules preserve typing. This is avoided in Dedukti with bracket arguments, which is not a completely safe feature and therefore is not implemented in Lambdapi. It is future work to improve Lambdapi to enable it to handle such cases. 

## Supported features

A non-exhaustive list of totally or partially supported features :

- Inductive types
- Recursive functions
- Prenex universe polymorphism
- Eta-conversion
- Records
- Copatterns
- Copattern matching coinduction

TODO :

- Correct errors when translating the standard library
- Rewrite rules
- Dream feature : translate Agda function definitions with clauses into definitions only using the elimination principle of inductive types

## Developers and references

The developpement of this translator was started by Guillaume Genestier and is done today by Thiago Felicissimo, both with the help of Jesper Cockx. The three main references about this translator are the following.

- G. Genestier. Encoding Agda Programs Using Rewriting. In Proceedings of the 5th International Conference on Formal Structures for Computation and Deduction, Leibniz International Proceedings in Informatics 167, 2020.
- T. Felicissimo. Representing Agda and coinduction in the lambda-pi calculus modulo rewriting. Master thesis, 2021.
- G. Genestier. Dependently-Typed Termination and Embedding of Extensional Universe-Polymorphic Type Theory using Rewriting. PhD thesis, 2020.
