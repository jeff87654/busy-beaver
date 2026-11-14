# BB32/: 32 states, 2 symbols

## Current entry: hydra32 (hydra machine by Argon, on mxdys's hydra31)

```
1RC1LT_---0LZ_0RD1RU_0RE0RW_0RF0RF_0RG1RS_0RH1RF_0RI1RI_0LJ1RH_1LK1L[_0RL1LO_1RM1RL_0RN1RV_1LJ1RM_0LP1LP_0LQ1LO_0LR1LA_1RD1LQ_0LZ1RF_0LA1LA_1RH0RM_0RM1RM_0RX1RY_1LO1RW_0RW1RW_1L[0LB_0L_1L\_0RD1L]_0LJ1L^_0L[1L__0RP1L`_0L]1LJ
```

States after Z are the next ASCII characters (`[` `\` `]` `^` `_` `` ` ``); `Z` is an
ordinary state here, and the only halting transition is B0 = `---`. Read the string in fixed-width rows of 6
characters (row i = characters 7i..7i+5), since `_` is also a state.

Halts from the blank tape (state B reading 0; N is the number of ones at the halt, σ = N or N + 1 by convention).
Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_{ω^ω^(ω^8·3)}(4) ≤ N + 2,  hence  f_{ω↑↑4}(8) < N        (hardy_score, sigma_lower_bound_w4_8)

No upper bound is proved.

- [`hydra32.md`](hydra32.md): the write-up (the machine, the run, the proof, verification, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1), built in CI (job `bb13-bb14`).
- [`../BB29/analysis/`](../BB29/analysis/): the analysis of the hydra game these machines play (written for hydra29,
  hydra31 and hydra33).

Found by **Argon** (a Google Gemini model run by the repository owner), 2026-11-09, from mxdys's
[hydra31](../BB31/README.md): up to a renaming of states, hydra32 is hydra31 (same hydra game, height
limit 5) with one transition redirected into one new state and another start state. Coq proof by Argon,
re-checked and packaged here (2026-11-13).

No superseded entries in this directory.
