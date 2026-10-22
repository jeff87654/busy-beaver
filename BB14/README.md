# BB14/: 14 states, 2 symbols

## Current entry: M14

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LN1RF_1LJ0RA_1RA0LH_1LG1LH_1RK0LM_1RZ0LE_0LE0RJ_1LH1LM_0LH0LL_0LG1LN

Halts from the blank tape; J0 (`1RZ` in the string) is the halt, so σ = N + 1, where N is the number of ones when J0
is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+2)(f_(ω+2)(f_(ω+2)(15))) < N + 1 = σ        (sigma_lower_bound)

and the stronger f_(ω+2)(f_(ω+2)(f_(ω+1)^15(f_ω(21)))) < σ (`sigma_lower_bound_strong`); the exact score is an
explicit recursion (`score_exact`; not evaluated). On paper (not machine-checked), this proved lower bound exceeds
T12a's and the published lower bounds for BB(14)–BB(16); it has not been compared with the f_(ω+2)-class
BB(17)/BB(18) champions.

- [`1RB1RA_..._0LH0LL_0LG1LN.md`](1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LN1RF_1LJ0RA_1RA0LH_1LG1LH_1RK0LM_1RZ0LE_0LE0RJ_1LH1LM_0LH0LL_0LG1LN.md):
  the write-up (how it works, the run, the score, comparisons, verification status, how it was found).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`, `sigma_lower_bound`,
  `sigma_lower_bound_strong`. About 30 s to compile; built and probed in CI (job `bb13-bb14`), which requires four
  closed `Print Assumptions` reports.
- [`tools/m14_writeup_chk.py`](tools/m14_writeup_chk.py): an independent literal simulator that re-checks every
  rule of the write-up on concrete instances.

Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity (2026-10-13);
re-checked here. M14 is a compressed descendant of Jacobzheng's 14-state f_(ω+1) champion (same evaluator, 20 of 28
transitions shared). Same architecture as M13 ([`../BB13/`](../BB13/)), with the outer counter reloaded twice.

No superseded entries in this directory.
