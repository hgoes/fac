fac
===
The **f**ast **a**iger **c**hecker is a tool developed for the course "Software Model Checking" @ TU Vienna in 2013.

Installation
------------
You need a recent (7.* should suffice) copy of the [glorious haskell compiler (GHC)](http://haskell.org/ghc) to compile this.
If you also have [cabal](http://haskell.org/cabal) installed, you can simply install the program by typing:

```
cabal install
```

If not, you have to use these three commands:

```
runghc Setup.hs configure
runghc Setup.hs build
runghc Setup.hs install
```

Issues
------
- [x] Right now, the program doesn't work with gcc-4.5, as explained in issue #1.
      A workaround is to provide cabal with the flag "BrokenGCC":
      ```
      cabal install -fBrokenGCC
      ```
      Or
      ```
      runghc Setup.hs configure -fBrokenGCC
      ```
      
