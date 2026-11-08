# BB20/: 20 states, 2 symbols

## Current entry: J20 (Jacobzheng's machine)

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

On paper (an argument, not a Coq lemma): far above every entry here with fewer states, which are all below f_(ω·2).
No proved upper bound; not yet reviewed by the bbchallenge community.

- [`1LH0LG_0LI1RC..._0LF1LT_0LF0LR.md`](1LH0LG_0LI1RC_0LD1LA_0RE1LD_1RQ1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0RF0LO_0RF1LP_0RF1LN_1LR1RQ_1RZ1LS_0LF1LT_0LF0LR.md):
  the write-up (the two lists, the expansion, the refill, the run, the mod-3 invariant, the score, verification,
  comparisons, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1, with a new 20-state setup `BB202.v`):
  `halt`, `score_exact`, `sigma_lower_bound`. About 25 s to compile; built and probed in CI (job `bb13-bb14`), which
  requires three closed `Print Assumptions` reports.
- [`tools/j20_writeup_chk.py`](tools/j20_writeup_chk.py): an independent simulator that re-checks the write-up's
  rules on concrete instances and follows the blank-tape run boundary by boundary.

Machine by Jacobzheng; analysis, Coq proof (2026-11-04), probe, write-up and packaging by this project.
