fac
===
The **f**ast **a**iger **c**hecker is a tool developed for the course "Software Model Checking" @ TU Vienna in 2013.

Installation
------------
You need a recent (7.* should suffice) copy of the [glorious haskell compiler (GHC)](http://haskell.org/ghc) to compile this.
If you also have [cabal](http://haskell.org/cabal) installed, you can simply install the program by typing:

```shell
cabal install
```

If not, you have to use these three commands:

```shell
runghc Setup.hs configure
runghc Setup.hs build
runghc Setup.hs install
```