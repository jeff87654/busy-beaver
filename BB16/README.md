# BB16/: 16 states, 2 symbols

## Current entry: M16_C

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RO0LO_1LP0LE_1RZ1LI

Halts from the blank tape; P0 (`1RZ` in the string) is the halt, so σ = N + 1, where N is the number of ones when P0
is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+2)(f_(ω+1)^114(f_(ω+2)^3(f_(ω+3)(9)))) < N,   σ = N + 1        (sigma_lower_bound)
    f_(ω+2)^4(f_(ω+3)(9)) < N                                         (sigma_bound_simple)

and the exact score N = p + a + 5 for the explicit pair (p, a) = `pa_16` (`score_exact`; not evaluated).

M16_C is M16_B (below) with one transition changed: O1 = `1RM` → `0LE`. O1 is read where M16_B ran its bridge, on the
tail `1 0 0 1 0 0 1^228` left after level 3. With `0LE`, the machine reads `1 0 0 1` as `1 1` followed by `0 1`: one
Kd1 step that leaves `0 1` behind. The cells after it then run as a D1 cycle, a Kd1 step, a D1 cycle and a Kd2 step:
three f_(ω+2) applications more than M16_B, before M16_B's 114 Kd1 steps, final f_(ω+2) cycle and halt.

On paper (an argument, not a Coq lemma): the proved bound is above M16_B's f_(ω+2)(f_(ω+3)(9)) = f_(ω+2)^10(9), but
**below the proved lower bound of the 14-state entry M14d_18** ([`../BB14/`](../BB14/)), f_(ω+2)^17(f_(ω+1)^2(3)):
M16_C's bound is at most f_(ω+2)^14(9), because f_(ω+1)^114(y) ≤ f_(ω+2)(y) for y ≥ 114 and f_(ω+3)(9) = f_(ω+2)^9(9),
while f_(ω+1)^2(3) > 9. Since BB(16) ≥ BB(14) + 2, M14d_18 gives a better proved lower bound for BB(16) than M16_C's
own proved bound. This compares proved lower bounds only; M16_C's true score is not proved smaller. It is also below
M17_B ([`../BB17/`](../BB17/)). The bbchallenge wiki's BB(16) row (checked 2026-11-04) is M16_B; M16_C is not yet
reviewed by the bbchallenge community.

- [`1LB1LA_1RC0LA..._1LP0LE_1RZ1LI.md`](1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RO0LO_1LP0LE_1RZ1LI.md):
  the write-up (the change and the O1=0LE bridge, the run, the size argument, verification, comparisons, credit).
- [`verify_m16c/`](verify_m16c/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `halt_f_omega3`,
  `score_exact`, `sigma_bound`, `sigma_bound_simple`, `sigma_lower_bound`. About 30 s to compile; built and probed in
  CI (job `bb13-bb14`), which requires six closed `Print Assumptions` reports.
- [`tools/m16c_writeup_chk.py`](tools/m16c_writeup_chk.py): an independent literal simulator that re-checks the
  opening, the bridge (against the ordinary Kd1 step), the other macro steps and the halt on concrete instances.

Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity (2026-11-03);
re-checked here.

## Previous entry: M16_B

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RO0LO_1LP1RM_1RZ1LI

Halts from the blank tape; P0 (`1RZ` in the string) is the halt, so σ = N + 1, where N is the number of ones when P0
is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+2)(f_(ω+3)(9)) < N,   σ = N + 1        (sigma_lower_bound)

and the exact score N = p + a + 5 for the explicit pair (p, a) = `pa_11` (`score_exact`; not evaluated).

M16_B uses the engine of Argon's DUMP_2552 (`BB16_fw4`, see [`../BB18/`](../BB18/)), with I0 changed and the three
reflection states N, O, P rewritten. The opening writes a finite program: nine level-3 steps (f_(ω+2) each,
f_(ω+3)(9) together), a bridge, 114 level-2 steps and one more f_(ω+2) cycle. When the program runs out, the machine
halts.

On paper (an argument, not a Coq lemma): f_(ω+2)(f_(ω+3)(9)) = f_(ω+2)^10(9) is above M14b's proved
f_(ω+2)^9(f_(ω+1)(f_(ω+1)(3))) ([`../BB14/`](../BB14/)), because f_(ω+2)(9) > f_(ω+1)(f_(ω+1)(3)). It is also above the
f_(ω+2)-class BB(17) champion (Jacobzheng). Neither has a proved upper bound. BB18_fw3 ([`../BB18/`](../BB18/)) stays
above it. Not yet reviewed by the bbchallenge community.

- [`1LB1LA_1RC0LA..._1LP1RM_1RZ1LI.md`](1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RO0LO_1LP1RM_1RZ1LI.md):
  the write-up (how it differs from BB16_fw4, the run, the halt, the size argument, verification, comparisons, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `halt_f_omega3`, `score_exact`,
  `sigma_lower_bound`. About a minute to compile; built and probed in CI (job `bb13-bb14`), which requires four
  closed `Print Assumptions` reports.
- [`tools/bb16_writeup_chk.py`](tools/bb16_writeup_chk.py): an independent literal simulator that re-checks the
  opening, `start_38` and the halt on concrete instances.

Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity (machine and
`BB16_halt_fw3.v`, received 2026-10-29); score theorems and packaging here.
