# BB16/: 16 states, 2 symbols

## Current entry: J16_w2 (Argon, on Jacobzheng's engine)

    1LG1LA_0LI1RC_0LD1LG_0RE1LD_0RM1RL_1RB1RF_1LH0LA_1RF0RN_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LG0RN_0RP1RO_1RZ1RM_1LB1LI

Halts from the blank tape; O0 (`1RZ` in the string) is the halt. It is read on a 0 and writes 1, so σ = N + 1, where
N is the number of ones when O0 is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω·2)(f_15(2)) < N,   σ = N + 1                                      (sigma_lower_bound)
    f_(ω+2)(f_(ω+1)^114(f_(ω+2)^3(f_(ω+3)(9)))) < N                       (beats_M16_C: M16_C's proved bound, below)
    f_(ω+2)^116(f_(ω+3)^3(9)) < N                                          (beats_M17_B: the BB(17) entry's)
    f_(ω+13)(20) < N                                                       (beats_J15: the BB(15) entry's)
    f_(ω+2)^30(f_(ω+1)(f_(ω+1)(3))) < N                                    (beats_M14_31: the BB(14) entry's)

and the exact score N = 2j + 4 for the j given by the machine's recursion (`score_exact`; not evaluated).

J16_w2 runs the 12-state core of Jacobzheng's J20 ([`../BB20/`](../BB20/)), renamed so that it starts in A, with the
period-3 rewriter of J15_fw13 ([`../BB15/`](../BB15/)) and one more state, P: a merged block of length ≡ 0 (mod 3)
now refills the outer list as [3, 2^k] instead of halting or giving [2^k], which lifts the level from f_(ω+13) to
f_(ω·2). The halt comes after two refills, at a residue the proof computes mod 9. Argon also gives the machine in
tree normal form, `1LB1LA_1LC0LA_..._0LP1LB_0RJ1LP`; that string is the same machine with the states renamed
(checked here by comparing the two tables, not in Coq).

So BB(16) has its best proved bound here. From 2026-11-08 to 2026-11-13 this was also the best proved bound for
BB(17), by BB(17) ≥ BB(16) + 1 (`beats_M17_B`); since then BB(17) has its own entry, Argon's J17_champ
([`../BB17/`](../BB17/)), whose proved bound states f_(ω·2)(f_15(2)) < N as well and adds f_(ω·2)(f_ω^3(f_14(2))) < N.
The bbchallenge wiki's Champions table has no BB(16) row (checked 2026-11-08). Not yet reviewed by the bbchallenge
community.

- [`1LG1LA_0LI1RC..._1RZ1RM_1LB1LI.md`](1LG1LA_0LI1RC_0LD1LG_0RE1LD_0RM1RL_1RB1RF_1LH0LA_1RF0RN_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LG0RN_0RP1RO_1RZ1RM_1LB1LI.md):
  the write-up (the table, the expansion and the refill, the run, the mod-3 and mod-9 residues, the size,
  verification, comparisons, credit).
- [`verify_j16/`](verify_j16/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`, `beats_J15`, `beats_M14_31`, `beats_M16_C`, `beats_M17_B`. About 40 s to compile; built and
  probed in CI (job `bb13-bb14`), which requires seven closed `Print Assumptions` reports.

Found and proved by Argon, a Google Gemini model run by the repository owner in Google's Antigravity (2026-11-08), by
compressing Jacobzheng's J19/J20 architecture; re-checked here, with the comparison file.

## Previous entry: M16_C

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
while f_(ω+1)^2(3) > 9. Since BB(16) ≥ BB(14) + 2, M14d_18 gave a better proved lower bound for BB(16) than M16_C's
own proved bound (J16_w2, above, is far above both). This compares proved lower bounds only; M16_C's true score is not proved smaller. It is also below
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

## Earlier entry: M16_B

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
