# Tutorials on Coq

See the README.md file in the parent directory for installation instructions
and link to the research papers.


Classical Logic
-------------------

Coq is originally based on a constructive logic.
Following the tradition, many users refuse to depend on classical axioms.

For certain mathematical proofs, e.g. in fundational geometry, being able
to precisely investigate the set of axioms that each result depends upon
is great.

For many other practical applications, however, there are mostly benefits
to using the classical axioms, which users of other proof assistants such
as HOL or Isabelle/HOL have been happily using for decades.

The main benefits of classical logic are:

- to avoid the need for dependently-typed programming, in particular for
  defining partial recursive functions;
- to allow for simpler statements of many definitions and equivalences;
- to allow proofs that simply wouldn't be possible outside of classical
  logic, e.g. to justify that the big-step characterization of divergence
  is equivalent to the small-step characterization of divergence;
  besides, for reasoning about real numbers, classical results appear to
  be a must-have.



The file `Classic.v` gives a tour of the classical axioms and their
practical applications.
