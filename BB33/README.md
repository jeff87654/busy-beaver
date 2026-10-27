# BB33/: 33 states, 2 symbols

## Current entry: BB33 (hydra machine by mxdys)

    1LH1L^_---0LC_1LR0LB_1RF1LE_0LD1LD_0R_1RG_1RN0RK_0RI1RJ_1L^1RH_0RH1RH_0RL1RM_1L`1RK_0RK1RK_0RO1RO_0L`1RN_1R_1La_0RZ0RZ_0LX1LS_0R_1LT_0L`1LU_0LR1LV_0LS1LW_0LT1LX_0R]1LY_0LV1L`_0R[1R\_0RN1RZ_0LC1RZ_0La1L^_0L]1L]_0RQ0RH_1LA1LR_0LP1LD

Halts from the blank tape (state B reading 0; N is the number of ones at the halt, σ = N or N + 1 by convention).
Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_{ω^ω^ω^ω^ω^3}(4) ≤ N + 2,  hence  f_{ω↑↑6}(3) < N        (sigma_lower_bound_w6)

The posted claim was BB(33) > f_{ω^ω^ω^ω^ω^ω}(3). No upper bound is proved.

- [`hydra33.md`](hydra33.md): the write-up (the hydra game, the run, the proof, verification, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1), built in CI (job `bb13-bb14`).
- [`../BB29/analysis/`](../BB29/analysis/): the analysis of all three hydra machines and its simulation checks.

Found by **mxdys** (posted, as an unverified AI-generated result, in the bbchallenge Discord, 2026-10-26).
Analysis and Coq proofs: this project, 2026-10-27. BB29, BB31 and BB33 are one family: the same hydra game with
height limits 3, 5 and 7.

No superseded entries in this directory.
