# BB10/: 10 states, 2 symbols

## Current entry: n1

    1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC

Halts from the blank tape; J0 (`1RZ` in the string) is the halt, so σ = N + 1, where N is the number of ones when J0
is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+1)((3T − 13)/7 − 2) < N < f_(ω+1)(6T),      T = 2↑^37 3        (fgh_level)

so its level is exactly ω+1. Also machine-checked: the exact score as an explicit recursion of Knuth arrows
(`score_exact`, `score_closed_unfolded`), N > G^((6T−19)/7)(33) with G(x) = 2↑^(x+1) 3 (`sigma_lower_bound`),
σ > Graham's number (`beats_graham`), and that it beats the BB(10) champion of Racheline (2024) against that
machine's own Coq-proved exact score (`beats_champion`).

- [`1RB0RA_..._0LJ0LI_1RZ0LC.md`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC.md): the write-up
  (how it works, the rules, the run, the exact score, size, comparisons, verification status, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1). `verify/BB10_n1_selfcontained.v` is one file
  that needs only the Coq standard library (`coqc BB10_n1_selfcontained.v`, about 13 minutes); `verify/multifile/`
  is the same development on busycoq (`compile_clean.sh`, about 20 minutes, then a probe that re-checks the table
  entry by entry). Not built in CI; the recorded from-scratch builds are in `verify/VERIFICATION.txt`.
- [`tools/bb10_n1_writeup_chk.py`](tools/bb10_n1_writeup_chk.py): an independent literal simulator that re-checks
  every rule of the write-up on concrete instances.
- [`screen/`](screen/): the heuristic candidate screen that found n1, with its data. Its verdicts are not claims.

Found and proved in this project, 2026-10-08. n1 runs the computation of champ35 (the BB(8) entry of this repository
until 2026-10-18, [`../BB8/`](../BB8/)) and then a countdown of about 0.43·T periods, each one f_ω-sized step.

No superseded entries in this directory.
