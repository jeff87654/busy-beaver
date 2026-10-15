# Compact formulas in arithmetic

> These notes describe an earlier development stage. See the
> [PA238 README](../../README.md) for the completed theorem and current build.

`CompactInPA238.v` starts the compact-to-PA direction with a concrete
arithmetic atom and a finite natural-deduction translation. Its beta remainder,
doubling-sequence power-of-two, and Ackermann bit formulas use only the pinned
PA signature `0`, successor, addition, multiplication, and equality. Source
`R(A,x)` translates to the container-first bit relation. Equality translates
to the explicit PA equality predicate. All source terms are variables.

The source includes substitution, binder-shift, and quantifier-instantiation
proofs; all fifteen natural-deduction constructors, including Peirce, are
translated with their finite context retained. The resulting theory is the
translated compact theory. No theorem equates it with ordinary PA yet.

The mathematical reference was inspected at the original source pin
`6f7f0c2f97703839e56a705bbf5da5a0e5c132cf`, in
`theory/cloud_20260930/ackermann_reverse_v1/filter.mm1` and
`interpretation.mm1`. Its fixed-formula comprehension induction uses code
zero initially and branches to `C+W` or `C` while doubling the power bound.
An all-index cutoff turns the bounded result into finite-support
comprehension. Separation uses the existing code as a support bound;
filtered adjunction uses `successor(A+D)`. Logical tails converting the
bounded filter to an unbounded support property and to the literal PAS
implications are included in the Coq leaf. The Coq proofs are original;
these reference sources and their receipt files are not vendored or treated
as Coq kernel acceptance.

The arithmetic witness producers remain explicit open proposition
definitions: power totality, power uniqueness and bounds, bit-position bound,
parameter-bearing bounded comprehension, empty set, adjunction, separation,
IR, the explicit equality base, and the pointed/collided schemas. Their existence is not assumed by a
claimed endpoint. The implication from a compact refutation to
`PA238.PAeq_inconsistent` remains open until these producers are constructed.

The initial leaf passed independent source review after its one inference
repair. It remains a draft awaiting the root's serialized Coq 8.20.1 check.
`PAOrder238.v` supplies an original finite PA induction derivation of order
irreflexivity; its source also passed independent review. `ir_from_position`
uses that derivation, leaving the bit-position arithmetic producer as its
single explicit prerequisite. Both new leaves still need native checking.
Its `Print Assumptions` requests are source
requests, not successful kernel reports. No native check is launched by its
author or by `check_paeq.py`.
