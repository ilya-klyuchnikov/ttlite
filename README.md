## SuperSpec v1.0 (alpha) - SuperCompiler for Martin-Löf Type Theory

SuperSpec v0.2 is an interpreter, type-checker and supercompiler for Martin-Löf Type Theory (TT).

The main feature of the supercompiler is that for any transformation performed by
the supercompiler a proof of correctness is provided.

## How to build

SuperSpec depends on [MRSC](https://github.com/ilya-klyuchnikov/mrsc) 0.5, so you need to install MRSC first:


    $ git clone git@github.com:ilya-klyuchnikov/mrsc.git
    $ cd mrsc
    $ sbt publish-local

Then you can build SuperSpec project:

    $ git clone git@bitbucket.org:lambdamix/superspec.git
    $ cd superspec
    $ sbt
    > test
    > eclipse
    > gen-idea

### SBT settings
Building/testing SuperSpec with default sbt settings may fail due to `OutOfMemory` issues. I use following settings for SBT (file `~/.sbtconfig`):

    SBT_OPTS="-Xms512M -Xmx1500M -Xss1M -XX:+CMSClassUnloadingEnabled -XX:+UseConcMarkSweepGC -XX:MaxPermSize=724M"

## Quick Start

There are two sub-projects:

* `tt` - REPL for TT.
* `tt-sc` - a simple supercompiler for TT (as an extension of REPL).

### TT REPL

To launch TT REPL, type in sbt console `tt/run`:

    > tt/run

Launching examples:

    TT> import "examples/core.hs";

Quitting REPL:

    TT > quit;

### Supercompiler

To launch TT REPL, type in sbt console `tt-sc/run`:

    > tt-sc/run

Launching examples:

    SUPERSPEC> import "examples/proofs/01.hs";

