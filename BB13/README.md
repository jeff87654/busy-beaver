# BB13/: 13 states, 2 symbols

## Current entry: M13_19

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LM1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LM1LK_0LG1LL

Halts from the blank tape; K0 (`1RZ` in the string) is the halt, so σ = N + 1, where N is the number of ones when K0
is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+2)^19(f_ω(3)) < N,   σ = N + 1                      (sigma_bound)
    f_(ω+2)^18(f_(ω+1)(f_(ω+1)(3))) < N                      (sigma_bound_fw1)

and, against the exact score of the previous entry M13b (below): M13b's halting tape holds exactly p + a + 5 ones
for (p, a) = `pa7`, and that number is below N (`beats_M13b_exact`, `beats_M13b_score`; the comparison file proves
p + a + 5 < f_(ω+2)^14(f_ω(3)) from the definitions of M13b's maps). Both machines have σ = N + 1, so M13_19's σ is
the larger.

M13_19 runs M12's engine and counters (as M13b does) with F0 sent to G instead of M, which frees M without breaking
any counter rule. E0, K, L and M then keep a stack of numbers on the right of the counter; a round with level d ≡ 1
(mod 3) pushes an entry, d ≡ 0 pops and drains the stack, and the machine halts when a drain flips the engine's
parity an odd number of times. That gives 19 f_(ω+2) rounds, against M13b's six. Not yet reviewed by the bbchallenge
community.

- [`1RB1RA_1RI1RC..._1RZ0LL_0LM1LK_0LG1LL.md`](1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LM1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LM1LK_0LG1LL.md):
  the write-up (the table, the stack, the 19 rounds, verification, comparisons, credit).
- [`verify_m13_19/`](verify_m13_19/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `sigma_bound`,
  `sigma_bound_fw1`, `beats_M13b` (against M13b's proved lower bound), the `_tnf` versions for the relabelled table,
  and `beats_M13b_exact`, `beats_M13b_score` (against M13b's exact score). Built and probed in CI (job `bb13-bb14`),
  which requires nine closed `Print Assumptions` reports.

Found and proved by Argon, a Google Gemini model run by the repository owner in Google's Antigravity (2026-11-09);
re-checked here, with the comparison file.

## Previous entry: M13b

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
  `Print Assumptions` reports. M13_19's comparison loads these two proof files (byte-identical copies in
  `verify_m13_19/multifile/`, checked by its `share_check.sh`).
- [`m13b_m14b_writeup_chk.py`](tools/m13b_m14b_writeup_chk.py): an independent literal simulator that re-checks every rule of the
  write-up on concrete instances (shared by M13b and M14b).

Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity (2026-10-28);
re-checked here.

## Earlier entry: M13

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
