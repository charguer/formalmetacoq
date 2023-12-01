# Arthur Charguéraud's Archive of Formal Metatheory in Coq

This repository contains a collection of formalizations
of programming language semantics and type soundness proofs.

Feel free to use them as templates for your own developments.


Contents
========

   - The folder `ln` contains locally nameless developments.
     See the paper "The Locally Nameless Representation" (JAR'11).
     http://www.chargueraud.org/research/2009/ln/main.pdf

     The folder `ln` includes type soundness proofs, w.r.t. omni-big-step and omni-small-step semantics.
     See the Omni-Semantics paper (TOPLAS'23).
     http://www.chargueraud.org/research/2022/omnisemantics/omnisemantics.pdf

   - The folder `pretty` contains pretty-big-step developments.
     See the Pretty-Big-Step paper (ESOP'13).
     http://www.chargueraud.org/research/2012/pretty/pretty.pdf

     The folder `pretty` also contains type soundness proofs, w.r.t. pretty-big-step semantics

   - Folder `tuto` contains a tutorial on the use of classical logic in Coq.


Compilation
===========

The files compile with Coq v8.18.

A tutorial on how to best configure Coq in VScode is available from:
https://chargueraud.org/teach/verif/install/install.html

The compilation of the files depends on the TLC library, available from `opam`.

```
  opam install coq-tlc
```

Alternatively, TLC may be installed by hand.

```
  git clone git@github.com:charguer/tlc.git
  make -j4 all && make install
```

To play the files interactively, enter one of the subfolders, compile
the scripts, then edit them, e.g., in VScode:

```
  cd ln
  make -j4
  code . &
```



License
=======

All files are distributed under the MIT X11 license. See the LICENSE file.

Authors
=======

All files in this repository are authored by Arthur Charguéraud.

