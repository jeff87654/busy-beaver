# BB20/: 20 states, 2 symbols

## Current entry: J20_cube (Argon, on Jacobzheng's engine)

    1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RT0RK_1LS1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_0LA0LA_1RZ1LK

Halts from the blank tape; T0 (`1RZ` in the string) is the halt. It is read on a 0 and writes 1, so σ = N + 1, where
N is the number of ones when T0 is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω·2)(f_(ω·2)(f_(ω·2)(f_5(2)))) < N,   σ = N + 1        (sigma_lower_bound)
    f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) < N                    (sigma_lower_bound: J20's proved bound, below)

and the exact score N = 2(j + 1) + 1 for the j given by the machine's recursion (`score_exact`; not evaluated).

J20_cube is the 19-state J19_sq ([`../BB19/`](../BB19/)) with one more state: its refill can grow the parked
sentinel to two cells instead of taking it in, so the third refill leaves one more for later. Four refills and three
rounds at level f_(ω·2); J19_sq has two such rounds and J20 (below) one.

Its proved bound is above J20's (stated in the same theorem with the same definitions), so BB(20) has its best
proved bound here. Comparisons with the exact scores of J20 and of J19_sq (BB(19) + 1): on paper only (the write-up,
section 4). B21 ([`../BB21/`](../BB21/)) stays far above. Not yet reviewed by the bbchallenge community.

- [`1LB0LM_1RC1RN..._0LA0LA_1RZ1LK.md`](1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RT0RK_1LS1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_0LA0LA_1RZ1LK.md):
  the write-up (the table, the two-cell sentinel, the run, the mod-3 invariant, the size, verification, comparisons,
  credit).
- [`verify_j20cube/`](verify_j20cube/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`. About a minute to compile; built and probed in CI (job `bb13-bb14`), which requires three
  closed `Print Assumptions` reports.

Found and proved by Argon, a Google Gemini model run by the repository owner in Google's Antigravity (2026-11-09), on
Jacobzheng's J19/J20 architecture; re-checked here.

## Previous entry: J20 (Jacobzheng's machine)

    1LH0LG_0LI1RC_0LD1LA_0RE1LD_1RQ1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0RF0LO_0RF1LP_0RF1LN_1LR1RQ_1RZ1LS_0LF1LT_0LF0LR

The bbchallenge wiki's BB(20) champion, found by Jacobzheng and listed on the wiki's Champions page with the lower
bound f_(ω·2)(f_(ω+2)^2(f_10(2))), marked "Not independently verified" (checked 2026-11-07). Proved here. Halts from
the blank tape; R0 (`1RZ` in the string) is the halt. It is read on a 0 and writes 1, so σ = N + 1, where N is the
number of ones when R0 is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) < N,   σ = N + 1        (sigma_lower_bound)

and the exact score N = 2j + 1 for the j given by the machine's explicit recursion (`score_exact`; not evaluated).
That is the wiki's claim, exactly. Here f_(ω·2)(n) = f_(ω+n)(n).

The machine keeps two digit lists, an inner one (f_k-class levels) and an outer one (f_(ω+k)-class levels), run by
one sweep engine. When the outer list is used up, a refill rebuilds it from the merged block of N ones, or halts,
depending on N mod 3. Every level map of both lists is x ↦ x + 1 (mod 3), so the residues are computed exactly: the
boot leads to a refill [1, 1, 2, 3], then to a refill [1, 2^k, 3] with k ≥ f_(ω+2)^2(f_10(2)), whose last digit is
reduced at outer level k (the f_(ω·2) step), and the third exhaustion halts.

On paper (an argument, not a Coq lemma): far above the entries with fewer states listed when it was added
(2026-11-07), which were all below f_(ω·2). No proved upper bound; not yet reviewed by the bbchallenge community. J20_cube (above)
has a higher proved bound.

R18a ([`../BB18/`](../BB18/)) is J20 with its four refill states removed (the refill merged into the expansion
rewriter): 18 states, the same f_(ω·2) class, and a lower proved bound, f_(ω·2)(f_ω(f_ω(f_10(2)))).

- [`1LH0LG_0LI1RC..._0LF1LT_0LF0LR.md`](1LH0LG_0LI1RC_0LD1LA_0RE1LD_1RQ1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0RF0LO_0RF1LP_0RF1LN_1LR1RQ_1RZ1LS_0LF1LT_0LF0LR.md):
  the write-up (the two lists, the expansion, the refill, the run, the mod-3 invariant, the score, verification,
  comparisons, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1, with a new 20-state setup `BB202.v`):
  `halt`, `score_exact`, `sigma_lower_bound`. About 25 s to compile; built and probed in CI (job `bb13-bb14`), which
  requires three closed `Print Assumptions` reports.
- [`tools/j20_writeup_chk.py`](tools/j20_writeup_chk.py): an independent simulator that re-checks the write-up's
  rules on concrete instances and follows the blank-tape run boundary by boundary.

Machine by Jacobzheng; analysis, Coq proof (2026-11-04), probe, write-up and packaging by this project.
