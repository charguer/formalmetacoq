# Arthur Charguéraud's Formal Metatheory in Coq


Description
===========

   - Folder `ln` contains locally nameless developments.
     See the paper "The Locally Nameless Representation" (JAR'11)
     http://www.chargueraud.org/research/2009/ln/main.pdf

   - Folder `pretty` contains pretty-big-step developments.
     See the paper Pretty Big Step Semantics (ESOP'13)
     http://www.chargueraud.org/research/2012/pretty/pretty.pdf

   - Folder `Tuto` contains course notes:

      + File `Classic` is a tutorial on using classical logic in Coq

      + File `Coind` are incomplete notes on coinduction


Compilation
===========

The files should compile with Coq v8.15.

The compilation of the files depends on the TLC library.
TLC is available from `opam`, package named `coq-tlc`.

TLC can also be installed by hand.

```
  git clone git@github.com:charguer/tlc.git
  cd src
  make install
```

The command for compiling all files:

```
   make -j4 all
```

The command `make -j4 vos` processes all files in a faster way,
to make them ready for interactive use.


License
=======

All files are distributed under the MIT X11 license. See the LICENSE file.

Authors
=======

See the AUTHORS file.
