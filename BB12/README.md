# BB12/: 12 states, 2 symbols

## Current entry: T12a

    1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RK0LC_0RL---_0RF1RZ

Halts from the blank tape in state L reading 1 (L1 = `1RZ` writes 1 on a 1, so σ = N, the number of ones at the
halt). Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+1)(f_(ω+1)(JJ − 2)) ≤ 6σ + 11,      JJ = (3T − 13)/7,      T = 2↑^37 3        (fgh_lower2)

and σ is larger than the exact score of n1 (`beats_n1`, against n1's Coq-proved exact score). No upper bound and no
exact score are proved. One transition (K1) is never read.

- [`1RB0RA_..._0RL---_0RF1RZ.md`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RK0LC_0RL---_0RF1RZ.md):
  the write-up (how it works, the run, the score, comparisons, verification status, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `sigma_lower_bound`,
  `score_ge_exact`, `beats_n1`, `fgh_lower2`. `verify/multifile/compile_clean.sh` rebuilds everything and runs a
  probe that re-checks the table entry by entry. Not built in CI: one 2.6 MB generated file takes about 2.8 h; the
  recorded from-scratch build is `verify/multifile/compile_clean.log`.

T12a is n1 ([`../BB10/`](../BB10/)) with two more states: it runs n1's whole computation, rebuilds a countdown from
n1's final values and runs n1's period loop a second time. Found and proved in this project, 2026-10-09/10.

No superseded entries in this directory.
