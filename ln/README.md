# Arthur Charguéraud's Archive of Locally Nameless Developments

See the README.md file in the parent directory for installation instructions
and link to the research papers.


Contents
========

Type soundness proofs:

- `STLC_Core`: simply typed lambda-calculus (STLC)
- `STLC_Core_WF`: STLC using reductin context (Wright & Felleisen's style)
- `STLC_Ref`: STLC plus references and nondeterminism
- `STLC_Exn`: STLC plus exceptions
- `STLC_Pat`: STLC plus basic pattern matching
- `STLC_Data`: a variant of STLC plus basic pattern matching
- `Fsub`: System-F with subtyping (POPLMark challenge)
- `CoC`: Calculus of constructions (dependent types)
- `ML_Core`: ML type schemes (types with only head universal quantification)
- `ML`: ML types with references and exceptions and pattern matching

Other results on semantics:

- `ISK_Confluence`: confluence of the minimalistic ISK system
- `CoC_ChurchRosser`: confluence of the calculus of constructions (dependent types)
- `Lambda_ChurchRosser`: confluence of the pure lambda-calculus
- `BigStep`: equivalence of big-step and small-step semantics
- `CPS`: correctness of the CPS translation

Other files:

- `Lambda_JAR_paper`: companion to the JAR'11 paper "The Locally Nameless Representation"
