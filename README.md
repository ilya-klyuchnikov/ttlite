## SuperSpec v1.0 - SuperCompiler for Martin-Löf Type Theory

SuperSpec v1.0 is an interpreter, type-checker and supercompiler for Martin-Löf Type Theory (TT).
It is structures into two sub-projects:

* TT Lite Core - lightweight and modular implementation of Martin-Löf Type Theory
(TT-Lite was designed with supercompilation in mind)
* TT Lite Supercompiler - very simple supercompiler for TT Lite.

The main feature of the supercompiler is that for any transformation performed by
the supercompiler a proof of correctness is provided.

## How to build

SuperSpec depends on [MRSC](https://github.com/ilya-klyuchnikov/mrsc) 0.5, so you need to install MRSC first:

    :::text
    $ git clone git@github.com:ilya-klyuchnikov/mrsc.git
    $ cd mrsc
    $ sbt publish-local

Then you can build SuperSpec project:

    :::text
    $ git clone git@bitbucket.org:lambdamix/superspec.git
    $ cd superspec
    $ sbt
    > test
    > eclipse
    > gen-idea

### SBT settings
Building/testing SuperSpec with default sbt settings may fail due to `OutOfMemory` issues.
I use following settings for SBT (file `~/.sbtconfig`):

    :::text
    SBT_OPTS="-Xms512M -Xmx1500M -Xss1M -XX:+CMSClassUnloadingEnabled -XX:+UseConcMarkSweepGC -XX:MaxPermSize=724M"

### SBT launcher
This project is build by SBT 0.13, so it requires that you have SBT launcher 0.13 (try `sbt --version` to know it).
If you have an old SBT launcher and do not want to update it for some reasons, then you can try to change
`project/build.properties` to:

    sbt.version=0.12.4

The symptom that you have an old SBT launcher is an exception like this:

    [ERROR] Terminal initialization failed; falling back to unsupported
        java.lang.IncompatibleClassChangeError:
        Found class jline.Terminal, but interface was expected

## Quick Start

There are two sub-projects:

* `ttlite-core` - TT Lite Core
* `ttlite-sc` - a simple supercompiler for TT Lite Core (as an extension of REPL).

### TT Lite (REPL)

To launch TT REPL, type in sbt console `ttlite-core/run`:

    :::text
    > ttlite-core/run

Load some definitions from examples:

    :::text
    TT> import "examples/nat.hs";

Try some simple computations:

    :::text
    TT> plus Zero Zero;
    Zero
    ::
    Nat;

    TT> plus Zero (Succ Zero);
    Succ Zero
    ::
    Nat;

You can look into definitions by evaluating them:

    :::text
    TT> plus;
    \ (a :: Nat) -> \ (b :: Nat) ->
        elim Nat (\ (c :: Nat) -> Nat) b (\ (c :: Nat) -> \ (d :: Nat) -> Succ d) a
    ::
    forall (a :: Nat) (b :: Nat) . Nat;

You can introduce new definitions directly in REPL:

    :::text
    TT> z = Zero;
    z
    ::
    Nat;

    TT> z;
    Zero
    ::
    Nat;

For definitions you can optionally specify a type (type checker will check it):

    :::text
    TT> m :: Nat; m = Succ Zero;
    m
    ::
    Nat;

(In REPL declaration with definition should fit the single line);

You can _assume_ a variable of a certain type (we will call it _assumed_ variable)
by specifying its type (a variable should start with `$`);

    :::text
    TT> $n :: Nat;
    Nat

    TT> plus $n $n;
    elim Nat (\ (a :: Nat) -> Nat) $n (\ (a :: Nat) -> \ (b :: Nat) -> Succ b) $n
    ::
    Nat;

Quitting REPL:

    :::text
    TT> quit;

### Syntax and Semantics of TT

Technical details of the implementation are described in the preprint "A supercompiler for type-theory".
However, the preprint just translates code of the current implementation into mathematical notation.

The proposed solution for understanding this project is:

* Sketch the preprint for grasping syntax and semantics (without details).
* Look into examples of how functions are defined (dir `examples`)
* Sketch some modules (`Function.scala`, `Nat.scala`, `DProduct.scala`)
for getting an idea how syntax and semantics are implemented.

Tutorial is on the way.

A program in TT Lite consists of the following statements:

* `id = term;` - definition
* `id :: term; id = term;` - typed definition;
* `import "file";` - loading of definitions from file
* `$id :: term;` - assumption of a variable of a certain type
* `term;` - just evaluating of a term;

### TT Supercompiler

To launch TT Supercompiler REPL, type in sbt console `ttlite-sc/run`:

    :::text
    > ttlite-sc/run

Launching examples:

    :::text
    TT-SC> import "examples/proofs/01.hs";

TT Supercompiler REPL introduces a new statement:

    :::text
    (t1, t2) = sc t;

The meaning of the new statement is that `t1` is a result of transformation of the `term` by the supercompiler,
`t2` is a proof that transformation is correct (i.e. `t2 :: Id a t t1` if `t :: a`).

`t1` and `t2` are put in the context as terms and available for further manipulations.

Here is an example of proving the equivalence of two expressions with assumed variables (`examples/proofs/01.hs`):

    :::text
    import "examples/nat.hs";
    import "examples/id.hs";

    -- proof of the associativity of addition
    -- plus x (plus y z) = plus (plus x y) z

    $x :: Nat;
    $y :: Nat;
    $z :: Nat;

    e1 = (plus $x (plus $y $z));
    e2 = (plus (plus $x $y) $z);
    (res1, proof1) = sc e1;
    (res2, proof2) = sc e2;

    -- associativity of addition using combinators
    -- check that t1 and t2 are supercompiled into the same expression
    eq_res1_res2 :: Id Nat res1 res2;
    eq_res1_res2 = Refl Nat res1;
    -- deriving equality
    eq_e1_e2 :: Id Nat e1 e2;
    eq_e1_e2 =
        proof_by_sc Nat e1 e2 res1 proof1 proof2;

`proof_by_sc` is a helper function defined in `examples/id.hs`. In this example correctness is checked by type-checker!

You can see input and output of supercompilation (as well as a proof):

    :::text
    TT-SC> import "examples/proofs/01.hs";

    TT-SC> e2;
    elim
        Nat
        (\ (a :: Nat) -> Nat)
        $z
        (\ (a :: Nat) (b :: Nat) -> Succ b)
        (elim Nat (\ (a :: Nat) -> Nat) $y (\ (a :: Nat) (b :: Nat) -> Succ b) $x)
    ::
    Nat;

    TT-SC> res2;
    elim
        Nat
        (\ (a :: Nat) -> Nat)
        (elim Nat (\ (a :: Nat) -> Nat) $z (\ (a :: Nat)  (b :: Nat) -> Succ b) $y)
        (\ (a :: Nat) (b :: Nat) -> Succ b)
        $x
    ::
    Nat;

    TT-SC> proof2;
    elim Nat
    (\ (a :: Nat) -> Id Nat
            (elim Nat (\ (b :: Nat) -> Nat) $z
                (\ (b :: Nat) -> \ (c :: Nat) -> Succ c)
                (elim Nat (\ (b :: Nat) -> Nat) $y
                    (\ (b :: Nat) -> \ (c :: Nat) -> Succ c)
                    a))
            (elim Nat (\ (b :: Nat) -> Nat)
                (elim Nat (\ (b :: Nat) -> Nat) $z
                    (\ (b :: Nat) -> \ (c :: Nat) -> Succ c)
                    $y)
                (\ (b :: Nat) -> \ (c :: Nat) -> Succ c)
                a))
    ...
    ::
    Id Nat
    (elim Nat (\ (a :: Nat) -> Nat) $z (\ (a :: Nat) -> \ (b :: Nat) -> Succ b)
        (elim Nat (\ (a :: Nat) -> Nat) $y
            (\ (a :: Nat) -> \ (b :: Nat) -> Succ b)
            $x))
    (elim Nat (\ (a :: Nat) -> Nat)
        (elim Nat (\ (a :: Nat) -> Nat) $z
            (\ (a :: Nat) -> \ (b :: Nat) -> Succ b)
            $y)
        (\ (a :: Nat) -> \ (b :: Nat) -> Succ b)
        $x);

The whole proof term is quite long (It is long since TT Lite performs normalization of terms and terms are printed
in normalized form). An interested person is encouraged to launch the supercompiler to see it.


In some sense, `sc` is just a function of the following type (type `A` is implicitly resolved from the context):

    :::text
    sc :: forall (A :: Set) (t :: A) . exists (t1 :: A) . Id A t t1;

