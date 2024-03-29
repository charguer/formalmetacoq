# Arthur Charguéraud's Archive of Omni-Semantics Developments

See the README.md file in the parent directory for installation instructions.

This folder contains formal developments around the omni-big-step and
omni-small-step semantics. These semantics are described in the TOPLAS'23 paper:
http://www.chargueraud.org/research/2022/omnisemantics/omnisemantics.pdf

The construction of type soundness proofs using omni-big-step and omni-small-step
semantics are described in the files `STLC_Ref_Soundness_OmniBig.v` and
`STLC_Ref_Soundness_OmniSmall.v` from the folder `../ln` of the present
repository.

The construction of a Separation Logic on top of an omni-big-step semantics
in described in the course "Separation Logic Foundations", Volume 6 of the
"Software Foundations" series. It is not reproduced here, only the proof
of the consequence and frame properties are established.

The files in the present folder contain proofs of the properties of the
omni-small and omni-big judgments, and proofs of equivalence with standard
small-step and big-step semantics. The developments are presented on a
standard, nondeterministic, imperative lambda-calculus.


Contents
========

Semantics formalized:

- `Syntax`: syntax of a nondeterministic, imperative lambda calculus, and of the entailment judgment
- `Small`: standard small-step semantics
- `Big`: standard big-step semantics
- `OmniSmall`: omni-small-step semantics, and eventually and divergence judgment,
   their properties, and equivalence with small-step semantics.
- `OmniBig`: omni-big-step semantics, inductive and coinductive,
   their properties, and equivalence with big-step semantics.
- `EquivSmallBig`: equivalence between standard small-step and standard big-step semantics
- `EquivOmni`: equivalence of omni-semantics and standard semantics

Formalization of a core Separation Logic:
- `SepLogicCommon`: heap predicates and entailment
- `SepLogicSmall`: separation logic built on top of standard small-step semantics
- `SepLogicOmniBig`: separation logic built on top of omni-big-step semantics
- `SepLogicOmniSmall`: separation logic built on top of omni-small-step semantics
- `SepLogicWithGhostOmniBig`: (work in progress) on the formalization of ghost state

Other files:

- `LibSepFmap`: a formalisation of finite maps, used to represent the mutable store.

