# Arthur Charguéraud's Archive of Pretty-Big-Step Developments

See the README.md file in the parent directory for installation instructions
and link to the research papers.


Contents
========

Languages formalized:

- `Lambda`: untyped lambda-calculus
- `Lambda_Typing`: simply typed lambda-calculus (STLC)
- `LambdaExn`: lambda-calculus with exceptions
- `LambdaExnSum`: lambda-calculus with sum and case constructs
- `CoreCaml`: a significant subset of Caml-light, not far from CakeML's language

For each language, the naming convention is:
- `_Syntax`: contains the syntax of the language
- `_Small`: contains a small-step semantics
- `_Big`: contains a big-step semantics
- `_Pretty`: contains a pretty-big-step semantics
- `_Interp`: contains a reference interpreter (i.e. functional big-step semantics)
- `_Err`: semantics including error rules
- `_Indexed`: variant of the pretty big-step with indices counting the number of steps
- `_Combi`: another variant using indices counting the number of steps
- `_EncodeExn`: experiment with exceptions encoded as sum types

Other files:

- `Common`: a few common definitions
