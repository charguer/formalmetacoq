# Arthur Charguéraud's Archive of Pretty-Big-Step Developments

See the README.md file in the parent directory for installation instructions
and link to the research papers.


Contents
========

Languages formalized:

- `Lambda`: lambda-calculus
- `LambdaExn`: lambda-calculus with exceptions
- `LambdaExnSum`: lambda-calculus with sum and case constructs
- `CoreCaml`: a significant subset of Caml-light, not far from CakeML's language

For each language, the syntax and the semantics are characterized as follows:

- `_Syntax`: contains the syntax of the language
- `_Err`: suffix indicated that the semantics includes error propagation rules
- `_Interp`: contains a reference interpreter, i.e. a functional big-step semantics
- `_Small`: contains a small-step semantics
- `_Big`: contains a big-step semantics
- `_Pretty`: contains a pretty-big-step semantics
- `_Indexed`: a experimental variant of pretty-big-step where the evaluation judgment is indexed with a natural number
- `_Combi`: another variant of pretty-big-step where the `terminate` constructor of behavior is indexed with a natural number

Moreover, several proofs are carried out with respect to pretty-big-style semantics:

- `_Typing`: simple types for the lambda-calculus (STLC)
- `_Sound`: type soundness proof for STLC
- `_EncodeExn`: source-to-source translation encoding exceptions into a monad
- `_Interp_Correct`: proof of correctness and completeness of an interpreter

Other files:

- `Common`: a few common definitions
- `LibHeap`: a formalization of the mutable store, used by `LambdaRef` and `CoreCaml`
