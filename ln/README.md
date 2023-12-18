# Arthur Charguéraud's Archive of Locally Nameless Developments

See the README.md file in the parent directory for installation instructions
and link to the research papers.


Type soundness proofs
-------------------

The folder contains a number of type soundness proofs:

- `STLC_Core`: simply typed lambda-calculus (STLC)
- `STLC_Ref`: STLC plus references and nondeterminism
- `STLC_Exn`: STLC plus exceptions
- `Fsub`: System-F with subtyping (POPLMark challenge)
- `CoC`: Calculus of constructions (dependent types)
- `ML`: ML types with references and exceptions and pattern matching

All the proofs are based the standart "preservation and progress" small-step approach,
except the files `STLC_Ref_Soundness_OmniBig.v` and `STLC_Ref_Soundness_OmniSmall.v` and `Fsub_Soundness_OmniSmall.v`,
which are based on novel techniques described in the Omni-Semantics paper (TOPLAS'23).
http://www.chargueraud.org/research/2022/omnisemantics/omnisemantics.pdf


Other results on semantics
-------------------

- `ISK_Confluence`: confluence of the minimalistic ISK system
- `CoC_ChurchRosser`: confluence of the calculus of constructions (dependent types)
- `Lambda_ChurchRosser`: confluence of the pure lambda-calculus
- `BigStep_Equivalence`: equivalence of big-step and small-step semantics
- `CPS_Correctness`: correctness of the CPS translation

Other files
-------------------

- `Lambda_JAR_paper`: companion to the JAR'11 paper "The Locally Nameless Representation"

