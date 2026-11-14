# BB17/: 17 states, 2 symbols

## Current entry: J17_champ (Argon, on Jacobzheng's engine)

    1LG1RH_0LI1RC_0LD1LQ_0RE1LD_0RP1RL_1RB1RF_1LQ1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LQ0RN_0LQ1RO_1RZ1RM_0LQ0RA_1LH0LG

Halts from the blank tape; O0 (`1RZ` in the string) is the halt. It is read on a 0 and writes 1, so σ = N + 1, where
N is the number of ones when O0 is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω·2)(f_ω^3(f_14(2))) < N,   σ = N + 1        (sigma_lower_bound)
    f_(ω·2)(f_15(2)) < N                            (sigma_lower_bound: J16_w2's proved BB(16) bound)

and the exact score N = 2j + 4 for the j given by the machine's recursion (`score_exact`; not evaluated). Both are
also proved for the same machine in tree normal form (`halt_tnf`, `sigma_lower_bound_tnf`).

J17_champ is Argon's J16_w2 ([`../BB16/`](../BB16/)) with three entries changed and its one-state refill exit
replaced by a two-state refill: Jacobzheng's J20 sweep engine and two lists, the period-3 rewriter, and an outer
accumulator that stays ≡ 1 (mod 3). The second refill comes after five applications of the outer head map instead
of two, so the last round runs at outer level ≈ f_ω^3(f_14(2)) instead of ≈ f_15(2). The halt after two refills
depends on G^5(4) mod 9, which the proof computes exactly through tables of the inner level maps mod 486.

Its proved bound is above BB(16) + 1's proved bound (J16_w2's f_(ω·2)(f_15(2)), stated in the same theorem with
the same definitions), so BB(17) has its best proved bound here again. In Coq it is also above J16_w2's exact score:
σ(J17_champ) = N + 1 > σ(J16_w2) + 1 (`beats_J16_exact`, `beats_J16_score`, against J16_w2's `score_exact`). The 18-state R18c ([`../BB18/`](../BB18/)) has a higher proved bound. Not yet
reviewed by the bbchallenge community.

- [`1LG1RH_0LI1RC..._0LQ0RA_1LH0LG.md`](1LG1RH_0LI1RC_0LD1LQ_0RE1LD_0RP1RL_1RB1RF_1LQ1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LQ0RN_0LQ1RO_1RZ1RM_0LQ0RA_1LH0LG.md):
  the write-up (the table, the rules, the refill, the run, the mod-3 and mod-9 residues, the size, verification,
  comparisons, credit).
- [`verify_j17/`](verify_j17/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`, `halt_tnf`, `sigma_lower_bound_tnf`, and the exact-score comparison `beats_J16_exact`,
  `beats_J16_score` (`BB17_J17_cmp.v`, with copies of J16_w2's proof). A few minutes to compile; built and probed in CI
  (job `bb13-bb14`), which requires seven closed `Print Assumptions` reports.

Found and proved by Argon, a Google Gemini model run by the repository owner in Google's Antigravity (2026-11-09), on
Jacobzheng's J19/J20 architecture; re-checked here.

## Previous entry: M17_B

From 2026-11-08 to 2026-11-13 BB(17) ≥ BB(16) + 1 (J16_w2, above M17_B's proved bound in Coq, `beats_M17_B`) was the
better proved bound for BB(17); M17_B stayed listed as the last 17-state entry. Argon's 17-state J17_w2 (proved
f_(ω·2)(f_13(2)) < N) is below J16_w2 and was not listed.

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
