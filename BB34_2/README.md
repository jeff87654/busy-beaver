# BB34_2/: 34 states, 2 symbols

**Folder name.** `BB34/` is BB(3,4) (3 states, 4 symbols), so this 34-state, 2-symbol entry lives in `BB34_2/` (BB(34, 2)).

## Current entry: hydra34 (hydra machine by Argon, on mxdys's hydra33)

```
1LC1LT_---0LS_1RD1LH_0RE0RC_0RF1RF_0RG1RE_1LA1RF_0LI1LI_0LJ1LH_0LK1LY_1RL1LJ_0RM0RV_0RN0RN_0RO1RR_0RP1RN_0RQ1RQ_0LA1RP_0LS1RN_1LT0LB_0La1LU_0RL1L\_0RX1RW_0RV1RV_1LH1RV_1RZ1L^_0RL1R[_1RP0RF_0LA1L]_0LT1L__0LY1LY_0LU1L`_0L\1La_0RI1Lb_0L_1LA
```

States after Z are the next ASCII characters (`[` `\` `]` `^` `_` `` ` `` `a` `b`); `Z` is an
ordinary state here, and the only halting transition is B0 = `---`. Read the string in fixed-width rows of 6
characters (row i = characters 7i..7i+5), since `_` is also a state.

Halts from the blank tape (state B reading 0; N is the number of ones at the halt, σ = N or N + 1 by convention).
Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_{ω^ω^ω^ω^ω^4}(5) ≤ N + 2,  hence  f_{ω↑↑6}(4) < N        (hardy_score, sigma_lower_bound_w6_4)

No upper bound for hydra34 is proved. hydra34 is above the exact score of hydra33 (BB(33)) in Coq: [`verify_vs33/`](verify_vs33/) proves an upper bound for hydra33's score and `BB34_beats_BB33` (N ≥ N(hydra33) + 3).

- [`hydra34.md`](hydra34.md): the write-up (the machine, the run, the proof, verification, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1), built in CI (job `bb13-bb14`).
- [`../BB29/analysis/`](../BB29/analysis/): the analysis of the hydra game these machines play (written for hydra29,
  hydra31 and hydra33).

Found by **Argon** (a Google Gemini model run by the repository owner), 2026-11-09, from mxdys's
[hydra33](../BB33/README.md): up to a renaming of states, hydra34 is hydra33 (same hydra game, height
limit 7) with one transition redirected into one new state and another start state. Coq proof by Argon,
re-checked and packaged here (2026-11-13).

No superseded entries in this directory.
