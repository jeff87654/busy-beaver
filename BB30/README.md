# BB30/: 30 states, 2 symbols

## Current entry: hydra30 (hydra machine by Argon, on mxdys's hydra29)

```
1RC1L[_---0LY_0RD1RW_0RE0RN_0RF0RF_0RG1RX_0RH1RF_0RI1RI_0LJ1RH_1LK1LU_0LL1LP_1LM0RD_0RD1LT_0RO1RV_1LP1RN_0LQ1LQ_0LR1LP_0LS1LA_1RD1LR_0RQ1LZ_0LT1LM_0RN1RN_1RH0R\_0LY1RF_1LU0LB_0LU1LJ_0LA1LA_0R^1R]_0R\1R\_1LJ1R\
```

States after Z are the next ASCII characters (`[` `\` `]` `^`); `Z` is an
ordinary state here, and the only halting transition is B0 = `---`. Read the string in fixed-width rows of 6
characters (row i = characters 7i..7i+5), since `_` is also a state.

Halts from the blank tape (state B reading 0; N is the number of ones at the halt, σ = N or N + 1 by convention).
Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_{ω^9}(10) ≤ N + 2,  hence  f_{ω^ω}(9) < N        (hardy_score, sigma_lower_bound_w2_9)

No upper bound is proved.

- [`hydra30.md`](hydra30.md): the write-up (the machine, the run, the proof, verification, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1), built in CI (job `bb13-bb14`).
- [`../BB29/analysis/`](../BB29/analysis/): the analysis of the hydra game these machines play (written for hydra29,
  hydra31 and hydra33).

Found by **Argon** (a Google Gemini model run by the repository owner), 2026-11-09, from mxdys's
[hydra29](../BB29/README.md): up to a renaming of states, hydra30 is hydra29 (same hydra game, height
limit 3) with one transition redirected into one new state and another start state. Coq proof by Argon,
re-checked and packaged here (2026-11-13).

No superseded entries in this directory.
