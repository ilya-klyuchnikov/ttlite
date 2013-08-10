# SuperSpec - Advanced SuperCompiler for dependent types

The big idea of the project is described in `notes.md`.

## SuperSpec v0.2 - Certified SuperCompiler for Martin-Löf Type Theory

SuperSpec v0.2 is an interpreter, type-checker and supercompiler for Martin-Löf Type Theory (TT).

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

## How to build

SuperSpec depends on [MRSC](https://github.com/ilya-klyuchnikov/mrsc) 0.5, so you need to install MRSC first:

```
$ git clone git@github.com:ilya-klyuchnikov/mrsc.git
$ cd mrsc
$ sbt publish-local
```

Then you can build SuperSpec project:

```
$ git clone git@bitbucket.org:lambdamix/superspec.git
$ cd superspec
$ sbt
> test
> eclipse
> gen-idea
```

### SBT settings

Building/testing SuperSpec with default sbt settings may fail due to `OutOfMemory` issues. I use following settings for SBT (file `~/.sbtconfig`):
```
SBT_OPTS="-Xms512M -Xmx1500M -Xss1M -XX:+CMSClassUnloadingEnabled -XX:+UseConcMarkSweepGC -XX:MaxPermSize=724M"
```


