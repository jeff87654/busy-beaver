# BB18/: 18 states, 2 symbols

## Current entry: M18_229round

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1LR_0RB1LI_1RZ1RR_1RN0LO

Halts from the blank tape; Q0 (`1RZ` in the string) is the halt. It is read on a 0 and writes 1, so σ = N + 1,
where N is the number of ones when Q0 is read. Machine-checked, with the standard fast-growing hierarchy and no
axioms:

    f_(ω+3)^229(9) < N,   σ = N + 1        (sigma_lower_bound)

and the exact score N = p + a + 8 for the explicit pair (p, a) = `pa_R229` (`score_exact`; not evaluated).

M18_229round is M18_4round (below) with O1, Q and R changed. The engine, the bounce and the f_(ω+3) round are
M18_4round's. What changes is how the round headers in the tail are read: N, Q and R read right through the
header into the block of 228 ones that the opening leaves at the end of the tail, which M18_4round never uses.
An odd round uses up two of those ones and leaves a header for an even round, and the even round leaves the odd
header again. So the reservoir gives 114 odd/even pairs: with the first round (M16_B's level-3 loop), 229
f_(ω+3) rounds in all. When the reservoir is empty, Q reads 0 and halts.

On paper (an argument, not a Coq lemma): f_(ω+3)^229(9) is above M18_4round's proved f_(ω+3)^4(9) (the BB(18) row
of the wiki's Champions table, checked 2026-11-04), and above f_(ω+4)(9) = f_(ω+3)^9(9). None of these has a proved
upper bound. Not yet reviewed by the bbchallenge community.

- [`1LB1LA_1RC0LA..._1RZ1RR_1RN0LO.md`](1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1LR_0RB1LI_1RZ1RR_1RN0LO.md):
  the write-up (the reader, the two sweeps, a round, the run, the score, verification, comparisons, credit).
- [`verify_m18r229/`](verify_m18r229/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`. About 40 s to compile; `probe.v` requires three closed `Print Assumptions` reports.
- [`tools/m18r229_writeup_chk.py`](tools/m18r229_writeup_chk.py): an independent literal simulator that re-checks
  the opening, the two sweeps, the bounce, the halt and the tail bookkeeping on concrete instances.

Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity (2026-11-03);
re-checked here.

## Previous entry: M18_4round

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1LN_0RB1LI_1RR0LO_0RO1RZ

Halts from the blank tape; R1 (`1RZ` in the string) is the halt. It is read on a 1 and writes 1, so σ = N, where N
is the number of ones when R1 is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+3)^4(9) < N = σ        (sigma_lower_bound)

and the exact score N = p + a + 233 for the explicit pair (p, a) = `pa_R4` (`score_exact`; not evaluated).

M18_4round is M17_B ([`../BB17/`](../BB17/)) with Q changed and one more state, R. Like M17_B, it sweeps the level
and the accumulator to the left end of the tape as (10) tokens and bounces back into the engine (P0 = `0RB`) for an
f_(ω+3) round. Q and R read the round headers in the tail differently, so the tail written by the opening holds
three headers instead of two: four f_(ω+3) rounds in all (the first is M16_B's level-3 loop), then the halt.

On paper (an argument, not a Coq lemma): f_(ω+3)^4(9) = f_(ω+2)^X(X) with X = f_(ω+3)^3(9) is above M17_B's proved
f_(ω+2)^116(X), and so above BB18_fw3's (below) and the f_(ω+2)-class BB(18) champion (Jacobzheng). None of these
has a proved upper bound. M18_229round (above) has a higher proved lower bound. Not yet reviewed by the
bbchallenge community.

- [`1LB1LA_1RC0LA..._1RR0LO_0RO1RZ.md`](1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1LN_0RB1LI_1RR0LO_0RO1RZ.md):
  the write-up (the core and the bounce, the two sweeps, a round, the run, the score, verification, comparisons,
  credit).
- [`verify_m18r4/`](verify_m18r4/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`. About 50 s to compile; built and probed in CI job `bb13-bb14` (which builds both `verify/`
  and `verify_m18r4/`); the job requires three closed `Print Assumptions` reports for this entry.
- [`tools/bb18_4round_writeup_chk.py`](tools/bb18_4round_writeup_chk.py): an independent literal simulator that
  re-checks the opening, the two sweeps, the bounce and the halt on concrete instances.

Found and proved by Argon, a Google Gemini model run by the repository owner in Google's Antigravity (2026-11-02);
re-checked here.

## Earlier entry: BB18_fw3

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
Neither has a proved upper bound. M17_B ([`../BB17/`](../BB17/)), with one fewer state, and M18_4round (above) have
higher proved lower bounds, and M18_229round higher still. Not yet reviewed by the bbchallenge community.

- [`1LB1LA_1RC0LA..._1LQ0RR_1RZ0LP.md`](1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_1RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RQ0RG_0LG1LP_0LO1LP_1LQ0RR_1RZ0LP.md):
  the write-up (the engine, the counter routine, the run, the score, verification, comparisons, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`, `sigma_lower_bound`,
  `sigma_lower_bound_fw3`. About 40 s to compile; built and probed in CI (job `bb13-bb14`), which requires four
  closed `Print Assumptions` reports.
- [`tools/bb18_writeup_chk.py`](tools/bb18_writeup_chk.py): an independent literal simulator that re-checks the
  write-up's rules on concrete instances.

Engine by Argon, a Google Gemini model run by the repository owner in Google's Antigravity (DUMP_2552, `BB16_fw4.v`);
18-state halter and Coq proof by this project (2026-10-29).
