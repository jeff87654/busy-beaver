# BB31/: 31 states, 2 symbols

## Current entry: BB31 (hydra machine by mxdys)

    0RK1RK_---0LC_1LQ0LB_1RF1LE_0LD1LD_0R\1RG_1RM0RK_0RI1RJ_1L[1RH_0RH1RH_0RL1RA_1L]1RK_0RN1RN_0L]1RM_1R\1L^_0RW0RW_0LU1LR_0R\1LS_0L]1LT_0LQ1LU_0RZ1LV_0LS1L]_0RX1RY_0RM1RW_0LC1RW_0L^1L[_0LZ1LZ_0RP0RH_1L_1LQ_0LO1LD_1LH1L[

Halts from the blank tape (state B reading 0; N is the number of ones at the halt, σ = N or N + 1 by convention).
Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_{ω^ω^ω^ω}(4) ≤ N + 2,  hence  f_{ω^ω^ω^ω}(3) < N        (sigma_lower_bound_w4)

The posted claim was BB(31) > f_{ω^ω^ω^ω}(3). No upper bound is proved.

- [`hydra31.md`](hydra31.md): the write-up (the hydra game, the run, the proof, verification, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1), built in CI (job `bb13-bb14`).
- [`../BB29/analysis/`](../BB29/analysis/): the analysis of all three hydra machines and its simulation checks.

Found by **mxdys** (posted, as an unverified AI-generated result, in the bbchallenge Discord, 2026-10-26).
Analysis and Coq proofs: this project, 2026-10-27. BB29, BB31 and BB33 are one family: the same hydra game with
height limits 3, 5 and 7.

No superseded entries in this directory.
