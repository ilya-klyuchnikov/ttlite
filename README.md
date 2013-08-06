# SuperSpec - Advanced SuperCompiler for dependent types

The big idea of the project is described in `notes.md`.

## SuperSpec v0.2 - Certified SuperCompiler for Martin-Löf Type Theory

SuperSpec v0.2 is an interpreter, type-checker and supercompiler for Martin-Löf Type Theory.

Look into tests for examples.

The features of SuperSpec (in random order, some features are in progress):

* True supercompilation by evaluation (Higher-Order Abstract Syntax)
* Extreme modularity
* Any residual program is provided with a proof that transformation is correct (that is, residual program is equivalent to a source program).
Proof is written in type theory and checked by the type checker (hence, certified supercompilation).
* (In progress) We extend the method of traditional supercompilation: since all programs are total, we can apply contraction to any free variable, and can get an amazing results - correctness is preserved.
* (In progress) No problem of correctness of multi-level supercompilation since all programs are total.
* Very interesting folding techniques - we can fold to eliminator with certain renaming only.
* Traditional supercompilation - focusing on the current neutral.
* Reconstruction of motive during residualization.
* (In progress) Dependent-types in Scala - via DSL + macros
