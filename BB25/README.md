# BB25/: 25 states, 2 symbols

## Current entry: W2PR (built on Racheline's B21)

    0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LV_0LH0LW_1LH0LX_1LH1LY_0LE1LR

Halts from the blank tape; R0 (`1RZ` in the string) is the halt. It is read on a 0 and writes 1, so σ = N + 1, where N
is the number of ones when R0 is read. Machine-checked, with no axioms:

    halts tm c0                                      (halt)
    f_(ω²)^5(4↑↑341) < N,   σ = N + 1                (sigma_lower_bound_wsq)
    f_(ω²)^3(4↑↑341) < N                             (beats_B21: B21's proved BB(21) bound)
    Fh^5(4↑↑341) < N                                 (sigma_lower_bound, the first published bound; Fh(n) = h_n(0))

with the standard fast-growing hierarchy below ω³ (f_(ω·(a+1))(n) = f_(ω·a+n)(n), f_(ω²)(n) = f_(ω·n)(n), as in
B21's `verify_w2/`).

W2PR is B21 ([`../BB21/`](../BB21/)) with U1 changed to `1LV` and a copy V, W, X, Y of B21's refill cycle R, S, T, U
(V0 = `0LH` where R0 halts). The refill then tests its accumulator mod 8 instead of mod 4, so the machine passes
refills #6 and #7, where B21 halts at #6, and halts at refill #8, after five big ω² phases instead of three.

Each of the five big phases applies f_(ω²) (B21 has three). This is the largest proved bound in the 2-symbol rows
here below BB(29), and through BB(25 + k) ≥ BB(25) + k also the best proved bound here for BB(26) to BB(28); the
wiki's Champions table has no rows between BB(21) and BB(29). `beats_B21` compares with B21's proved lower bound, not
with an upper bound on B21's σ. Not yet reviewed by the bbchallenge community.

- [`0LI0LF_0RJ1RG..._1LH1LY_0LE1LR.md`](0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LV_0LH0LW_1LH0LX_1LH1LY_0LE1LR.md):
  the write-up (the change to B21, the mod-8 refill, the run, the residue schedule, verification, size, credit).
- [`verify_w2/`](verify_w2/): the ω² bound (2026-11-08): `halt`, `sigma_lower_bound`, `sigma_lower_bound_wsq`,
  `beats_B21`. All files but `BB25_W2PR_bound.v` and `BB25_W2PR_w2.v` are byte-identical copies of `verify/`'s and
  `../BB21/verify_w2/`'s (`share_check.sh`). Built and probed in CI (job `bb13-bb14`), four closed `Print Assumptions`
  reports.
- [`verify/`](verify/): the first published proofs (busycoq `bd2e36f`, Coq 8.20.1, with a new 25-state setup `BB252.v`): `halt`,
  `sigma_lower_bound`, and `BB25_W2PR_run.abstract_finalW`. Seven files are B21's layers, byte-identical to
  `../BB21/verify/multifile/`'s (`share_check.sh`). About 3 minutes to compile; built and probed in CI (job
  `bb13-bb14`), which requires three closed `Print Assumptions` reports.
- [`tools/w2pr_writeup_chk.py`](tools/w2pr_writeup_chk.py): an independent simulator that re-checks the mod-8 refill on
  every residue class, the identity with B21 up to the relabelling, and the residue schedule.

This project's machine and proof (2026-11-07/08), built on Racheline's B21; the ω² machinery is Racheline's.
