# BB19/: 19 states, 2 symbols

## Current entry: M19_fw4

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_1RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0RG_0LG1LP_0LO1LP_1LS0RR_1RZ0LP_0LR1LS

Halts from the blank tape; R0 (`1RZ` in the string) is the halt, so σ = N + 1, where N is the number of ones when R0
is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+4)(f_(ω+2)(114)) < N,   σ = N + 1        (sigma_lower_bound)
    f_(ω+4)(114) < N                              (sigma_lower_bound_fw4)

and the exact score N = p + a + 6 for the explicit pair (p, a) = `pa_final` = `Kcycle pa_init` (`score_exact`; not
evaluated).

The machine is Argon's 16-state engine DUMP_2552 (`BB16_fw4`, which never halts and grows by f_(ω+3) per
stack-reflection pass), with N0 changed and three new states Q, R and S. In the first pass, S walks left over the
accumulator block and R breaks the last pair of the stack, so the pass leaves the block of a₀ + 7 ones parked to
the right as a unary counter. Every later pass erases two parked 1s and runs a full f_(ω+3) pass. After a₀/2 + 4
passes one parked 1 is left; Q erases it and R halts. Since a₀ is huge, that is f_(ω+4).

On paper (an argument, not a Coq lemma): f_(ω+4)(f_(ω+2)(114)) = f_(ω+3)^n(n) with n = f_(ω+2)(114) is above the
proved bound f_(ω+3)^4(9) of M18_4round, the BB(18) entry ([`../BB18/`](../BB18/)). The wiki's BB(19) row is empty.
This is **not** a BB(20) record: the wiki's BB(20) champion (Jacobzheng, f_(ω+7)(f_(ω+7)(5))) is far larger. No
proved upper bounds; not yet reviewed by the bbchallenge community.

- [`1LB1LA_1RC0LA..._1RZ0LP_0LR1LS.md`](1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_1RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0RG_0LG1LP_0LO1LP_1LS0RR_1RZ0LP_0LR1LS.md):
  the write-up (the engine, accumulator parking, the run, the score, verification, comparisons, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`, `sigma_lower_bound`,
  `sigma_lower_bound_fw4`. About 40 s to compile; built and probed in CI (job `bb13-bb14`), which requires four
  closed `Print Assumptions` reports.
- [`tools/bb19_writeup_chk.py`](tools/bb19_writeup_chk.py): an independent literal simulator that re-checks the
  write-up's rules on concrete instances.

Engine, 19-state halter and Coq proof by Argon, a Google Gemini model run by the repository owner in Google's
Antigravity (2026-11-02); probe, write-up, packaging and re-check by this project.
