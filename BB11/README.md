# BB11/: 11 states, 2 symbols

## Current entry: M11b

    1RG0LH_1RK1RC_0LD1LA_0RE1LD_0LI1RF_1RZ0RG_1RB1RG_1LA1LH_0LK0LJ_1LH1LI_1LJ1RE

Halts from the blank tape in state F reading 0 (F0 = `1RZ` writes a 1 on a 0, so σ = N + 1, where N is the number
of ones at the halt). Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+1)(f_ω(f_ω(5))) < N                                   (sigma_lower_bound_m11)

and the exact number of ones at the halt is given by an explicit recursion (`score_exact`). No upper bound is
proved. M11b beats n1, the BB(10) entry, against n1's proved upper bound f_(ω+1)(f_ω(44)) (`M11_beats_n1`).

- [`1RG0LH_1RK1RC..._1LJ1RE.md`](1RG0LH_1RK1RC_0LD1LA_0RE1LD_0LI1RF_1RZ0RG_1RB1RG_1LA1LH_0LK0LJ_1LH1LI_1LJ1RE.md): the write-up.
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound_m11`, `sigma_lower_bound_64` (built in CI, job `bb13-bb14`, 18 s) and `M11_beats_n1`
  (local build, about 6 minutes, on copies of n1's files).

M11b runs the W engine of M12 ([`../BB12/`](../BB12/)) with one outer counter. Found and proved by Argon (a Google
Gemini model run by the repository owner), 2026-10-26; the Coq files were re-checked and repaired here (see the
write-up's credit section).

No superseded entries in this directory.
