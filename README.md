# SuperSpec project

The goal of SuperSpec projec is to repeat [HipSpec](https://github.com/danr/hipspec) with following modifications:

1. We use type theory (TT) instead of haskell, so there is no need for step of tranflating a program into
first-order logic, we use TT directly.
2. Instead of external theorem prover we use supercompilation. What is novel, is driving of pairs of configurations.
3. Multi-result and multi-level superompilations blossom in this project.

## Current status

There is a very simple ad-hoc proof-of-concept implementation of a very simple theorem prover based on supercompilation
methods.

Working example:


    sbt
    > run-main superspec.SuperSpecREPL
    LP > :l nats.pi
    LP > :sc plus <1> 0, <1>
    LP > |__natElim (\ a -> forall b :: Nat . Nat) (\ a -> a) (\ a -> \ b -> \ c -> Succ (b c)) <1> Zero, <1>
           |Local(1) = ElimBranch(Zero,Map())
           |__Zero, Zero
           |Local(1) = ElimBranch(Succ(Inf(Free(Local(102)))),Map(Local(102) -> Inf(Free(Local(1)))))
           |__Succ (natElim (\ a -> forall b :: Nat . Nat) (\ a -> a) (\ a -> \ b -> \ c -> Succ (b c)) <102> Zero), Succ <102>
             |Leibniz: Inf(Free(Global(Succ)))
             |__natElim (\ a -> forall b :: Nat . Nat) (\ a -> a) (\ a -> \ b -> \ c -> Succ (b c)) <102> Zero, <102>*
         \ a -> natElim
             (\ b -> Eq Nat
                     (natElim (\ c -> forall d :: Nat . Nat) (\ c -> c)
                         (\ c -> \ d -> \ e -> Succ (d e))
                         b
                         Zero)
                     b)
             (Refl Nat Zero)
             (\ b -> \ c -> leibniz Nat Nat (\ d -> Succ d)
                         (natElim (\ d -> forall e :: Nat . Nat) (\ d -> d)
                             (\ d -> \ e -> \ f -> Succ (e f))
                             b
                             Zero)
                         b
                         c)
             a

In this example SuperSpec drives a pair of expressions trying to proof their equivalence. The result term is a proof
of it. We can copy-paste result term (and add types for now) - and it can be type-checked! - see the bottom of `nats.pi`.

## The plan

The initial results are exciting. But, it is pragmatic to issue results step-by-step. The supercompiler for TT is built
in the novel way and it deserves its own preprint. Also, it seems that some parts of TT supercompiler are unclear and
it is easier to understand these parts first in simple supercompiler (not theorem prover for TT) and only then continue
to work on theorem prover. So,

1. Build a simple TT supercompiler - types, eliminators,
2. Multi-resultness - any free variable can be abstracted using eliminators, we can prove (for example) commutativity of
addition.
3. Multi-level supercompiler - in TT there is no problem of correctness of three-level supercompilation - since any
program is terminating.

So, for now I switch to the new branch `pi` which is dedicated only for TT superocompilation (without theorem proving).