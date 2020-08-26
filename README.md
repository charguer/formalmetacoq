# Arthur's Formal Metatheory in Coq


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

The files should compile with Coq v8.10, v8.11 or v8.12.

The compilation of the files depends on the TLC library.
TLC is available from `opam`, package named `coq-tlc`.

TLC can also be installed by hand.
For Coq v8.10 or more recent:

```
  git clone git@github.com:charguer/tlc.git
  cd src
  make install
```


License
=======

All files in TLC are distributed under the MIT X11 license. See the LICENSE file.

Authors
=======

See the AUTHORS file.
