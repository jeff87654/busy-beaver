# BB18/: 18 states, 2 symbols

## Current entry: BB18_fw3

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_1RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RQ0RG_0LG1LP_0LO1LP_1LQ0RR_1RZ0LP

Halts from the blank tape; R0 (`1RZ` in the string) is the halt, so σ = N + 1, where N is the number of ones when R0
is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+2)(f_(ω+3)(114)) < N,   σ = N + 1        (sigma_lower_bound)
    f_(ω+3)(114) < N                              (sigma_lower_bound_fw3)

and the exact score N = p + a + 5 for the explicit pair (p, a) = `Kpass1 pa_init` (`score_exact`; not evaluated).

The machine is Argon's 16-state engine DUMP_2552 (`BB16_fw4`, which never halts and grows by f_(ω+3) per
stack-reflection pass), with N0 changed and two new states Q and R. At the start of the first pass, Q and R plant a
marker cell and keep the next pass start at the same head position. The first pass then runs in full, and at the
start of the second pass Q finds the marker and R halts.

On paper (an argument, not a Coq lemma): f_(ω+3)(114) = f_(ω+2)^114(114) is far above M14b's proved
f_(ω+2)^9(f_(ω+1)(f_(ω+1)(3))) ([`../BB14/`](../BB14/)) and the f_(ω+2)-class BB(17)/BB(18) champions (Jacobzheng).
Neither has a proved upper bound. Not yet reviewed by the bbchallenge community.

- [`1LB1LA_1RC0LA..._1LQ0RR_1RZ0LP.md`](1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_1RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RQ0RG_0LG1LP_0LO1LP_1LQ0RR_1RZ0LP.md):
  the write-up (the engine, the counter routine, the run, the score, verification, comparisons, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`, `sigma_lower_bound`,
  `sigma_lower_bound_fw3`. About 40 s to compile; built and probed in CI (job `bb13-bb14`), which requires four
  closed `Print Assumptions` reports.
- [`tools/bb18_writeup_chk.py`](tools/bb18_writeup_chk.py): an independent literal simulator that re-checks the
  write-up's rules on concrete instances.

Engine by Argon, a Google Gemini model run by the repository owner in Google's Antigravity (DUMP_2552, `BB16_fw4.v`);
18-state halter and Coq proof by this project (2026-10-29).
