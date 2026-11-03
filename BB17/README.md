# BB17/: 17 states, 2 symbols

## Current entry: M17_B

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1LN_0RB1LI_1RZ1LO

Halts from the blank tape; Q0 (`1RZ` in the string) is the halt, so σ = N + 1, where N is the number of ones when Q0
is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+2)^116(f_(ω+3)^3(9)) < N,   σ = N + 1        (sigma_lower_bound)
    f_(ω+3)^3(9) < N                                  (sigma_lower_bound_fw3_3)

and the exact score N = p + a + 5 for the explicit pair (p, a) = `pa_final` (`score_exact`; not evaluated).

M17_B keeps the 13-state core A–M of M16_B ([`../BB16/`](../BB16/)) and the slots N1, O0, P1, changes N0, O1 and P0,
and adds a state Q. Where M16_B runs its bridge, M17_B sweeps the level and the accumulator to the left end of the
tape as (10) tokens, and P0 = `0RB` bounces back into the engine at a fixed start level. The engine then runs one
f_(ω+2) step per token: an f_(ω+3) round. The tail written by the opening holds two round headers, so there are three
f_(ω+3) rounds in all (the first is M16_B's level-3 loop), then 114 Kd1 steps, one more f_(ω+2) cycle and the halt.

On paper (an argument, not a Coq lemma): f_(ω+3)^3(9) is above the proved lower bounds of BB18_fw3 (the previous
BB(18) entry, f_(ω+2)(f_(ω+3)(114))) and of M16_B (f_(ω+2)^10(9)), and far above the f_(ω+2)-class BB(17) champion
(Jacobzheng). None of these has a proved upper bound. Not yet reviewed by the bbchallenge community.

- [`1LB1LA_1RC0LA..._0RB1LI_1RZ1LO.md`](1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1LN_0RB1LI_1RZ1LO.md):
  the write-up (the core, the sweep and the bounce, a round, the run, the score, verification, comparisons, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`, `sigma_lower_bound`,
  `sigma_lower_bound_fw3_3`. About 40 s to compile; built and probed in CI (job `bb13-bb14`), which requires four
  closed `Print Assumptions` reports.
- [`tools/bb17_writeup_chk.py`](tools/bb17_writeup_chk.py): an independent literal simulator that re-checks the
  opening, the sweep, the bounce and the halt on concrete instances.

Found and proved by Argon, a Google Gemini model run by the repository owner in Google's Antigravity (2026-11-02);
re-checked here.
