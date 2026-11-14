# BB18/: 18 states, 2 symbols

## Current entry: R18c (this project's machine, in the R18a family; Coq proof by Argon)

    1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_1LQ0LO_0LR1LP_1LQ1LN_1LF0LM_0RC1RZ

Halts from the blank tape; R1 (`1RZ` in the string) is the halt. It is read on a 1 and writes 1, so σ = N, where N
is the number of ones when R1 is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω·2)(f_(ω+1)(f_4(2))) < N = σ        (sigma_lower_bound)
    f_(ω·2)(2·f_ω^9(35)) < N                (sigma_lower_bound: J18_w2_C's proved bound, below)

and the exact score N = 2(j + 1) + 1 for the j given by the machine's recursion (`score_exact`; not evaluated). Both
are also proved for the same machine in tree normal form (`halt_tnf`, `sigma_lower_bound_tnf`).

R18c is R18a (below) with six entries changed: the exits of the period-3 rewriter N0, O0, P0 and the dispatch states
Q and R. The engine, the two lists and J20's mod-3 schedule are unchanged (exactly two refills, then the halt, at
level f_(ω·2)). The new exits give a different expansion head map and a longer refill, [2, 2] at the boot and
[3, 2^(k+1)] at the second exhaustion, so the first round already ends at outer level 1, and the last round runs at
an outer level of order f_(ω+1)(f_4(2)), where J18_w2_C's runs at one of order f_ω^15 (paper estimate).

Its proved bound is above J18_w2_C's (stated in the same theorem with the same definitions), so BB(18) has its best
proved bound here. Comparison with J18_w2_C's exact score: on paper only (the write-up, section 4). The 19-state
J19_sq ([`../BB19/`](../BB19/)) has a higher proved bound. Not yet reviewed by the bbchallenge community.

- [`1LH0LG_0LI1RC..._1LF0LM_0RC1RZ.md`](1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_1LQ0LO_0LR1LP_1LQ1LN_1LF0LM_0RC1RZ.md):
  the write-up (the table, the changes to R18a, the rules, the refill, the run, the mod-3 invariant, the size,
  verification, comparisons, credit).
- [`verify_r18c/`](verify_r18c/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`, `halt_tnf`, `sigma_lower_bound_tnf`. About a minute to compile; built and probed in CI (job
  `bb13-bb14`), which requires five closed `Print Assumptions` reports.

This project's machine: found on 2026-11-07 by the search for compressions of Jacobzheng's J20 that produced R18a
(then listed as an unproved variant); Coq proof by Argon, a Google Gemini model run by the repository owner in
Google's Antigravity (2026-11-09); re-checked here.

## Previous entry: J18_w2_C (Argon, on Jacobzheng's engine)

    0LB1LF_0RC1LB_0RD1RM_1LE0RN_1LF1LE_1LG0LE_1RH1RP_1RI1RH_0LJ1RA_1LK1LJ_0LL1LJ_1RM1RC_0RM0RH_1LE1RO_1RZ1RD_0LF0RQ_0LH1RR_0LF1RP

Halts from the blank tape; O0 (`1RZ` in the string) is the halt. It is read on a 0 and writes 1, so σ = N + 1, where
N is the number of ones when O0 is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω·2)(2·f_ω^9(35)) < N,   σ = N + 1         (sigma_lower_bound)
    f_(ω·2)(f_ω(f_ω(f_10(2)))) < N                (beats_R18a: R18a's proved bound, below)
    f_(ω·2)(f_15(2)) < N                          (beats_J16: the BB(16) entry's)

and the exact score N = 2j + 2 for the j given by the machine's recursion (`score_exact`; not evaluated).

J18_w2_C is written in tree normal form; under other names, its 12-state engine is Jacobzheng's J20 core
([`../BB20/`](../BB20/)), as in R18a. The other six states are a three-state expansion whose level maps are
x ↦ x + 1 (mod 3) for every residue (one residue is merged back in a single pass), and a three-state refill. As in
J20 and R18a, the mod-3 invariant makes the third merged block land in the halting class: exactly two refills, then
the halt, at level f_(ω·2). Its first refill comes later than R18a's, after G has been iterated G(10) + 1 times, so
its argument to f_(ω·2) is f_ω^9(35)-sized instead of f_ω(f_ω(f_10(2))).

In Coq (`beats_R18a`, `beats_J16`): N is above R18a's and J16_w2's proved bounds, so from 2026-11-08 to 2026-11-13
BB(18) and, by BB(19) ≥ BB(18) + 1, BB(19) had their best proved bounds here. R18c (above) has a higher proved bound.
Not yet reviewed by the bbchallenge community.

- [`0LB1LF_0RC1LB..._0LH1RR_0LF1RP.md`](0LB1LF_0RC1LB_0RD1RM_1LE0RN_1LF1LE_1LG0LE_1RH1RP_1RI1RH_0LJ1RA_1LK1LJ_0LL1LJ_1RM1RC_0RM0RH_1LE1RO_1RZ1RD_0LF0RQ_0LH1RR_0LF1RP.md):
  the write-up (the table, the expansion and the refill, the run, the mod-3 invariant, the size, verification,
  comparisons, credit).
- [`verify_j18c/`](verify_j18c/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`, `beats_R18a`, `beats_J16`. About 45 s to compile; built and probed in CI (job `bb13-bb14`),
  which requires five closed `Print Assumptions` reports.

Found and proved by Argon, a Google Gemini model run by the repository owner in Google's Antigravity (2026-11-08), by
compressing Jacobzheng's J20 by two states; re-checked here, with the comparison file.

## Earlier entry: R18a (derived from Jacobzheng's J20)

    1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0LQ0LO_1LR1LP_0LQ1LN_0RO1LB_0LL1RZ

Halts from the blank tape; R1 (`1RZ` in the string) is the halt. It is read on a 1 and writes 1, so σ = N, where N
is the number of ones when R1 is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω·2)(f_ω(f_ω(f_10(2)))) < N = σ        (sigma_lower_bound)
    f_(ω+7)(f_(ω+7)(5)) < N                   (beats_J19: J19's proved BB(19) bound)
    f_(ω+3)^229(9) < N                         (beats_M18_229: M18_229round's proved bound, below)

and the exact score N = 2c + 2 for the c given by J20's recursion (`score_exact`; not evaluated).

R18a is Jacobzheng's 20-state BB(20) champion J20 ([`../BB20/`](../BB20/)) with its four refill states removed. J20's
refill rewriter was the same period-3 cycle as its expansion rewriter, so in R18a the refill reuses the expansion's
walker and rewriter, and two new states, Q and R, read the cell left of the rewriter's exit: the blank in an
expansion, the far-left marker in a refill (E0 = `0RH` keeps the marker apart in a refill). Rows A–P are J20's except
E0, N0, O0 and P0. The two lists, the engine and J20's mod-3 schedule are unchanged: exactly two refills, then the
halt, at level f_(ω·2).

In Coq (`beats_J19`, `beats_M18_229`): N is above J19's and M18_229round's proved lower bounds (neither of those has a
proved upper bound). So BB(19) ≥ BB(18) + 1 is the better proved bound for BB(19) too. J20 ([`../BB20/`](../BB20/)) has
a higher proved bound. Not yet reviewed by the bbchallenge community.

- [`1LH0LG_0LI1RC..._0RO1LB_0LL1RZ.md`](1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0LQ0LO_1LR1LP_0LQ1LN_0RO1LB_0LL1RZ.md):
  the write-up (the changes to J20, the refill, the run, the mod-3 invariant, the score, verification, comparisons,
  credit).
- [`verify_r18a/`](verify_r18a/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`, `beats_J19`, `beats_M18_229`. About 30 s to compile; built and probed in CI (job `bb13-bb14`),
  which requires five closed `Print Assumptions` reports.
- [`tools/r18a_writeup_chk.py`](tools/r18a_writeup_chk.py): an independent simulator that re-checks the write-up's
  rules on concrete instances and the first outer boundaries of the blank-tape run.

This project's machine (2026-11-07), derived from Jacobzheng's J20: found by a search for a compression of J20,
proved in Coq by adapting this repository's J20 proof.

## Earlier entry: M18_229round

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
upper bound. R18a (above) has a higher proved lower bound. Not yet reviewed by the bbchallenge community.

- [`1LB1LA_1RC0LA..._1RZ1RR_1RN0LO.md`](1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1LR_0RB1LI_1RZ1RR_1RN0LO.md):
  the write-up (the reader, the two sweeps, a round, the run, the score, verification, comparisons, credit).
- [`verify_m18r229/`](verify_m18r229/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`. About 40 s to compile; `probe.v` requires three closed `Print Assumptions` reports.
- [`tools/m18r229_writeup_chk.py`](tools/m18r229_writeup_chk.py): an independent literal simulator that re-checks
  the opening, the two sweeps, the bounce, the halt and the tail bookkeeping on concrete instances.

Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity (2026-11-03);
re-checked here.

## Earlier entry: M18_4round

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
higher proved lower bounds, M18_229round higher still, and R18a higher again. Not yet reviewed by the bbchallenge community.

- [`1LB1LA_1RC0LA..._1LQ0RR_1RZ0LP.md`](1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_1RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RQ0RG_0LG1LP_0LO1LP_1LQ0RR_1RZ0LP.md):
  the write-up (the engine, the counter routine, the run, the score, verification, comparisons, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`, `sigma_lower_bound`,
  `sigma_lower_bound_fw3`. About 40 s to compile; built and probed in CI (job `bb13-bb14`), which requires four
  closed `Print Assumptions` reports.
- [`tools/bb18_writeup_chk.py`](tools/bb18_writeup_chk.py): an independent literal simulator that re-checks the
  write-up's rules on concrete instances.

Engine by Argon, a Google Gemini model run by the repository owner in Google's Antigravity (DUMP_2552, `BB16_fw4.v`);
18-state halter and Coq proof by this project (2026-10-29).
