# BB13/: 13 states, 2 symbols

## Current entry: M13b

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LH1LK_1RZ0LH

Halts from the blank tape; M0 (`1RZ` in the string) is the halt, so σ = N + 1, where N is the number of ones when M0
is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+2)^6(f_(ω+1)(f_(ω+1)(3))) < N + 1 = σ        (sigma_lower_bound)

and the exact score N = p + a + 5 for the explicit pair (p, a) = `pa7` (`score_exact`; not evaluated).

M13b is M12 ([`../BB12/`](../BB12/)) with one more state. M12's halt becomes a reload that recycles the tape
into a fresh counter, and a 3-adic countdown on the level allows three reloads before the halt. On paper, its
proved lower bound exceeds M13's (below), M12's and M14's; it has not been compared with the f_(ω+2)-class
BB(17)/BB(18) champions.

- [`1RB1RA_1RI1RC..._0LH1LK_1RZ0LH.md`](1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LH1LK_1RZ0LH.md): the write-up (how it works, the run, the score, verification, relation to other entries).
- [`verify_m13b/`](verify_m13b/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`. About 30 s to compile; built and probed in CI (job `bb13-bb14`), which requires three closed
  `Print Assumptions` reports.
- [`m13b_m14b_writeup_chk.py`](tools/m13b_m14b_writeup_chk.py): an independent literal simulator that re-checks every rule of the
  write-up on concrete instances (shared by M13b and M14b).

Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity (2026-10-28);
re-checked here.

## Previous entry: M13

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_0LG1RI_1RE0RH_1LF0RC_1RM0LE_1LA1LE_0LL1LB_0RM1LL_1RZ1RH

Halts from the blank tape; M0 (`1RZ` in the string) is the halt, so σ = N + 1, where N is the number of ones when M0
is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+2)(f_ω(20)) < N + 1 = σ        (sigma_lower_bound_strong)

and the exact score as an explicit recursion (`score_exact`; not evaluated). On paper (not machine-checked), this
proved lower bound exceeds T12a's ([`../BB12/`](../BB12/)) and the published lower bounds for BB(14)–BB(16); it has
not been compared with the f_(ω+2)-class BB(17)/BB(18) champions.

- [`1LB1LA_..._0RM1LL_1RZ1RH.md`](1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_0LG1RI_1RE0RH_1LF0RC_1RM0LE_1LA1LE_0LL1LB_0RM1LL_1RZ1RH.md):
  the write-up (how it works, the run, the score, comparisons, verification status, how it was found).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`, `sigma_lower_bound`,
  `sigma_lower_bound_strong`. About 30 s to compile; built and probed in CI (job `bb13-bb14`), which requires four
  closed `Print Assumptions` reports.
- [`tools/m13_writeup_chk.py`](tools/m13_writeup_chk.py): an independent literal simulator that re-checks every
  rule of the write-up on concrete instances.
- [`search/`](search/): Argon's search programs (unchanged), with what each does and what was re-run.

Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity (2026-10-14);
re-checked here. M13 adapts the evaluator of Jacobzheng's 14-state f_(ω+1) champion.
