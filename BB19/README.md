# BB19/: 19 states, 2 symbols

**Not a record.** The bbchallenge wiki's Champions page (checked 2026-11-04) lists a BB(19) champion by Jacobzheng
with the lower bound f_(ω+7)^2(5), for
`1RQ1RL_0LI1RC_0LD1LF_0RA1LD_1RB1RE_1LH0LG_1LF1LG_1RE1RM_1LJ1LI_0LK1LI_1RL1RA_0RL0RE_0LN1RM_1LO0LO_1RE1LP_1LN1LN_1LR1RQ_1RZ1LS_0LE0LR`
(marked "Not independently verified"). Both machines below are far below it. They are kept as our best 19-state
machines with complete Coq proofs. (Earlier versions of this page said the wiki's BB(19) row was empty; corrected
2026-11-04.)

## Current entry: M19_fw4_A

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1RR_0RB1LI_1RS0LQ_1LN0LR_0LR1RZ

Halts from the blank tape; S1 (`1RZ` in the string) is the halt. It is read on a 1 and writes 1, so σ = N, the
number of ones when S1 is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+4)(f_(ω+3)(9)) < N = σ        (sigma_lower_bound)

and the exact score N = p + a + 234 for the explicit pair (p, a) = `pa_final` (`score_exact`; not evaluated).

The machine is built on the core of M17_B and M18_4round ([`../BB17/`](../BB17/), [`../BB18/`](../BB18/)): rows A–N
and P are theirs, with the left-end bounce P0 = `0RB`. O1 is changed and Q, R, S are new. After the first f_(ω+3)
round, a parking sweep erases the accumulator a and leaves a + 5 blank cells between the round header and a fixed
wall of 228 ones. Every later round is a full f_(ω+3) round that moves the header one cell towards the wall. When
the header reaches the wall, S reads its first 1 and halts. Since a ≥ 8 · f_(ω+3)(9) + 6, that is f_(ω+4).

On paper (an argument, not a Coq lemma): f_(ω+4)(f_(ω+3)(9)) is above M19_fw4's proved f_(ω+4)(f_(ω+2)(114)) (below)
and above the BB(18) entries here ([`../BB18/`](../BB18/)). It is far below Jacobzheng's BB(19) champion. No proved
upper bounds; not yet reviewed by the bbchallenge community.

- [`1LB1LA_1RC0LA..._1LN0LR_0LR1RZ.md`](1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1RR_0RB1LI_1RS0LQ_1LN0LR_0LR1RZ.md):
  the write-up (the core, the two sweeps, the rounds, the run, the score, verification, comparisons, credit).
- [`verify_m19a/`](verify_m19a/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`. About 50 s to compile; built and probed in CI (job `bb13-bb14`), which requires three closed
  `Print Assumptions` reports.
- [`tools/m19a_writeup_chk.py`](tools/m19a_writeup_chk.py): an independent literal simulator that re-checks the
  write-up's rules on concrete instances.

Machine and Coq proof by Argon, a Google Gemini model run by the repository owner in Google's Antigravity
(2026-11-03); probe, write-up, packaging and re-check by this project.

## Previous entry: M19_fw4

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
proved bound f_(ω+3)^4(9) of M18_4round ([`../BB18/`](../BB18/)). It is not a BB(19) record (see the top of this
page; corrected 2026-11-04). No proved upper bounds; not yet reviewed by the bbchallenge community.

- [`1LB1LA_1RC0LA..._1RZ0LP_0LR1LS.md`](1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_1RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0RG_0LG1LP_0LO1LP_1LS0RR_1RZ0LP_0LR1LS.md):
  the write-up (the engine, accumulator parking, the run, the score, verification, comparisons, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`, `sigma_lower_bound`,
  `sigma_lower_bound_fw4`. About 40 s to compile; built and probed in CI (job `bb13-bb14`), which requires four
  closed `Print Assumptions` reports.
- [`tools/bb19_writeup_chk.py`](tools/bb19_writeup_chk.py): an independent literal simulator that re-checks the
  write-up's rules on concrete instances.

Engine, 19-state halter and Coq proof by Argon, a Google Gemini model run by the repository owner in Google's
Antigravity (2026-11-02); probe, write-up, packaging and re-check by this project.
