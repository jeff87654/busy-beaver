# BB29/: 29 states, 2 symbols

## Current entry: BB29 (hydra machine by mxdys)

    0LP1LD_---0LC_1LR0LB_1RF1LE_0LD1LD_0R[1RG_1RN0RK_0RI1RJ_1LZ1RH_0RH1RH_0RL1RM_1L\1RK_0RK1RK_0RO1RO_0L\1RN_1R[1LA_0RV0RV_0LT1LS_0R[1LT_0RY1LU_0LR1L\_0RW1RX_0RN1RV_0LC1RV_0LA1LZ_0LY1LY_0RQ0RH_1L]1LR_1LH1LZ

Halts from the blank tape (state B reading 0; N is the number of ones at the halt, σ = N or N + 1 by convention).
Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_{ω^ω}(3) < N                (sigma_lower_bound)

The exact count is N = T₄(S)(1) + 1 (`score_exact`, T an explicit recursion). The posted claim was BB(29) > f_{ω^ω}(3). No upper bound is proved.

- [`hydra29.md`](hydra29.md): the write-up (the hydra game, the run, the proof, verification, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1), built in CI (job `bb13-bb14`).
- [`analysis/`](analysis/): the analysis of all three hydra machines written before the proofs (`REPORT.md`, the
  specification the Coq comments cite) and the simulation scripts that check every rule (`python check_all.py`).

Found by **mxdys** (posted, as an unverified AI-generated result, in the bbchallenge Discord, 2026-10-26).
Analysis and Coq proofs: this project, 2026-10-27. BB29, BB31 and BB33 are one family: the same hydra game with
height limits 3, 5 and 7.

No superseded entries in this directory.
