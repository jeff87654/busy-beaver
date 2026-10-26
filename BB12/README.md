# BB12/: 12 states, 2 symbols

## Current entry: M12

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LH1LK

Halts from the blank tape in state K reading 0 (K0 = `1RZ` writes a 1 on a 0, so σ = N + 1, where N is the number
of ones at the halt). Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+2)(f_(ω+1)(f_(ω+1)(3))) < σ                         (sigma_lower_bound_m12)

and the exact number of ones at the halt is given by an explicit recursion (`score_exact`). No upper bound is
proved. M12 is one level of the fast-growing hierarchy above T12a below; that comparison is on paper (T12a has no
proved upper bound).

- [`1RB1RA_1RI1RC..._0LH1LK.md`](1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LH1LK.md): the write-up.
- [`verify_m12/`](verify_m12/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound_strong`, `sigma_lower_bound_m12`. Built in CI (job `bb13-bb14`, about a minute).

M12 shares its A–D, G and H rows with M14 ([`../BB14/`](../BB14/)). Found and proved by Argon (a Google Gemini
model run by the repository owner), 2026-10-26; the Coq files were re-checked here.

## Previous entry: T12a

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

