## TT Lite [![Build Status](https://travis-ci.org/ilya-klyuchnikov/ttlite.png)](https://travis-ci.org/ilya-klyuchnikov/ttlite)

TT Lite is an interpreter, type-checker and supercompiler for Martin-Löf's Type Theory (TT).
It is structured into two sub-projects:

* TT Lite Core - lightweight and modular implementation of Martin-Löf's Type Theory
(TT Lite was designed with supercompilation in mind)
* TT Lite Supercompiler - a very simple supercompiler for TT Lite.

The main feature of the supercompiler is that for any transformation performed by
the supercompiler a proof of correctness is provided.

TT Lite also supports exporting into Agda, Coq and Idris languages, which allows to verify
performed transformations and generated proofs independently of TT Lite.

The technical internals of TT Lite are described in the preprint:

* Ilya Klyuchnikov, Sergei Romanenko. **TT Lite: a
  supercompiler for Martin-Löf’s type theory**. Keldysh Institute preprints, 2013, No. 73, 28 p.
  <http://library.keldysh.ru/preprint.asp?id=2013-73&lg=e>

The fundamental principles of our approach to certifying supercompilation are described in the following paper:

* Ilya Klyuchnikov, Sergei Romanenko.
  **Certifying supercompilation for Martin-Löf's type theory**. PSI14, preprint version.
  <http://pat.keldysh.ru/~ilya/ttlite-psi2014.pdf>

## How to build / Test

TT Lite is built using SBT. You need to install SBT first from [here](http://www.scala-sbt.org).

    $ git clone git@github.com:ilya-klyuchnikov/ttlite.git
    $ cd ttlite
    $ sbt
    > test

TTLite contains integration tests which invoke Agda, Coq and Idris compilers for generated proofs:

    > it:test

In order to run these test you should have `agda`, `coqc` and `idris` executables in path.

## Quick Start

There are two sub-projects:

* `core` - TT Lite Core
* `sc` - TT Lite SC

### TTLite Core

To launch TT Core REPL, type in sbt console `core/run`:

    > core/run

Load some definitions from examples:

    TT> import examples/nat;

Try some simple computations:

    TT> plus Zero Zero;
    Zero
    :
    Nat;

    TT> plus Zero (Succ Zero);
    Succ Zero
    :
    Nat;

You can look into definitions by evaluating them:

    TT> plus;
    \ (a : Nat) -> \ (b : Nat) ->
        elim Nat (\ (c : Nat) -> Nat) b (\ (c : Nat) -> \ (d : Nat) -> Succ d) a
    :
    forall (a : Nat) (b : Nat) . Nat;

You can introduce new definitions directly in REPL:

    TT> z = Zero;
    z
    :
    Nat;

    TT> z;
    Zero
    :
    Nat;

For definitions you can optionally specify a type (type checker will check it):

    TT> m : Nat; m = Succ Zero;
    m
    :
    Nat;

(In REPL a declaration with a definition should fit a single line);

You can _assume_ a variable of a certain type (we will call it _assumed_ variable)
just by specifying its type (a variable should start with `$`);

    TT> $n : Nat;
    Nat

    TT> plus $n $n;
    elim Nat (\ (a : Nat) -> Nat) $n (\ (a : Nat) -> \ (b : Nat) -> Succ b) $n
    :
    Nat;

Quitting REPL:

    TT> quit;

### Syntax and Semantics of TT

Technical details of this implementation are described in the preprint
[TT Lite: a supercompiler for Martin-Löf's type theory](http://library.keldysh.ru/preprint.asp?id=2013-73&lg=e).
However, the preprint just translates code of the current implementation into mathematical notation.

The proposed way to get into this project is:

* Sketch the preprint for grasping syntax and semantics (without details).
* Look into examples of how functions are defined (dir [`examples`](examples/))
* Sketch some modules ([`Function.scala`](ttlite-core/src/main/scala/ttlite/core/Function.scala),
[`Nat.scala`](ttlite-core/src/main/scala/ttlite/core/Nat.scala),
[`DProduct.scala`](ttlite-core/src/main/scala/ttlite/core/DProduct.scala))
for getting an idea how syntax and semantics are implemented.

Tutorial is on the way.

A program in TT Lite consists of the following statements:

* `id = term;` - definition
* `id : term; id = term;` - typed definition;
* `import "file";` - loading of definitions from file
* `$id : term;` - assumption of a variable of a certain type
* `term;` - just evaluating of a term;

### TT Lite SC (supercompiler)

To launch TT Lite SC REPL, type in sbt console `ttlite-sc/run`:

    > sc/run

Launching examples:

    TT-SC> import examples/hosc/10;

TT Lite SC REPL introduces a new statement:

    (t1, t2) = sc t;

The meaning of the new statement is that `t1` is a result of transformation of a term `t` by the supercompiler,
`t2` is a proof that transformation is correct (i.e. `t2 : Id A t t1` if `t : A`).

`t1` and `t2` are put in the context as terms and available for further manipulations.

Here is an example of proving the equivalence of two expressions with assumed variables (`examples/hosc/10.hs`):

    import examples/nat;
    import examples/id;

    -- proof of the associativity of addition
    -- plus x (plus y z) = plus (plus x y) z

    $x : Nat;
    $y : Nat;
    $z : Nat;

    e1 = (plus $x (plus $y $z));
    e2 = (plus (plus $x $y) $z);
    (res1, proof1) = sc e1;
    (res2, proof2) = sc e2;

    -- associativity of addition using combinators
    -- check that t1 and t2 are supercompiled into the same expression
    eq_res1_res2 : Id Nat res1 res2;
    eq_res1_res2 = Refl Nat res1;
    -- deriving equality
    eq_e1_e2 : Id Nat e1 e2;
    eq_e1_e2 = proof_by_sc Nat e1 e2 res1 proof1 proof2;

`proof_by_sc` is a helper function defined in `examples/id.hs`. In this example correctness is checked by type-checker!

You can see input and output of supercompilation (as well as a proof):

    TT-SC> import examples/hosc/10;

    TT-SC> e2;
    elim
        Nat
        (\ (a : Nat) -> Nat)
        $z
        (\ (a : Nat) (b : Nat) -> Succ b)
        (elim Nat (\ (a : Nat) -> Nat) $y (\ (a : Nat) (b : Nat) -> Succ b) $x)
    :
    Nat;

    TT-SC> res2;
    elim
        Nat
        (\ (a : Nat) -> Nat)
        (elim Nat (\ (a : Nat) -> Nat) $z (\ (a : Nat)  (b : Nat) -> Succ b) $y)
        (\ (a : Nat) (b : Nat) -> Succ b)
        $x
    :
    Nat;

    TT-SC> proof2;
    elim Nat
    (\ (a : Nat) -> Id Nat
            (elim Nat (\ (b : Nat) -> Nat) $z
                (\ (b : Nat) -> \ (c : Nat) -> Succ c)
                (elim Nat (\ (b : Nat) -> Nat) $y
                    (\ (b : Nat) -> \ (c : Nat) -> Succ c)
                    a))
            (elim Nat (\ (b : Nat) -> Nat)
                (elim Nat (\ (b : Nat) -> Nat) $z
                    (\ (b : Nat) -> \ (c : Nat) -> Succ c)
                    $y)
                (\ (b : Nat) -> \ (c : Nat) -> Succ c)
                a))
    ...
    :
    Id Nat
    (elim Nat (\ (a : Nat) -> Nat) $z (\ (a : Nat) -> \ (b : Nat) -> Succ b)
        (elim Nat (\ (a : Nat) -> Nat) $y
            (\ (a : Nat) -> \ (b : Nat) -> Succ b)
            $x))
    (elim Nat (\ (a : Nat) -> Nat)
        (elim Nat (\ (a : Nat) -> Nat) $z
            (\ (a : Nat) -> \ (b : Nat) -> Succ b)
            $y)
        (\ (a : Nat) -> \ (b : Nat) -> Succ b)
        $x);

The whole proof term is quite long (it is long since TT Lite performs normalization of terms and terms are printed
in normal form). An interested person is encouraged to launch the supercompiler to see it.

### Interactive development

There is no editor or IDE plugin for TT Lite yet. So the only possibility to speedup development is to make a
change in a file and reload this file in REPL. For this purpose there is a special statement:

    reload file;

Examples:

    reload examples/id;

For now, this statemenent reloads a specified file, but **do not** reload its dependencies.

### Why `*.hs` ?

If you look into examples, you will notice that all of TT Lite examples are in files with extension `.hs`.
There is a very simple reason for this: syntax of TT Lite is quite close to Haskell and GitHub performs quite
good syntax coloring fot TT Lite files if they have extension `.hs`. That's it :)

### Further reading

* [Change notes](/tech-notes/changes.md)
