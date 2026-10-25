# Vendored subset of the Coq Library of Undecidability Proofs

Source: <https://github.com/uds-psl/coq-library-undecidability>, branch `coq-8.20`, commit
`70dfc56f33a6e4835281044e68aa68279989047e` (2024-09-18). License: MPL-2.0 (see `LICENSE`).

`theories/` holds 41 unmodified source files: the dependency closure of `FOL/PA.v`,
`FOL/Arithmetics/NatModel.v`, `FOL/Arithmetics/DeductionFacts.v`, `FOL/Arithmetics/TarskiFacts.v`,
`FOL/Deduction/FullNDFacts.v`, `FOL/Syntax/Facts.v` and `FOL/Semantics/Tarski/FullSoundness.v`. Each file is
byte-identical to that commit (LF line endings). `ORDER.txt` is the compile order; `../../coq/build.py` compiles
them with logical root `Undecidability` and `-set "Default Proof Using = Type"`, as in the library's `_CoqProject`.
