# BB21/: 21 states, 2 symbols

## Current entry: B21 (Racheline's machine)

    0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR

The bbchallenge wiki's BB(21) champion, found by Racheline and listed on the wiki's Champions page with the lower
bound f_(ω²)^2(4↑↑341), marked "Not independently verified" (checked 2026-11-08). Its halting and the wiki's bound
(with one more f_(ω²)) are proved here. Halts
from the blank tape; R0 (`1RZ` in the string) is the halt. It is read on a 0 and writes 1, so σ = N + 1, where N is
the number of ones when R0 is read. Machine-checked, with no axioms:

    halts tm c0                                           (halt)
    f_(ω²)(f_(ω²)(f_(ω²)(4↑↑341))) < N,   σ = N + 1        (sigma_lower_bound_wsq3)
    f_(ω²)(f_(ω²)(4↑↑341)) < N                            (sigma_lower_bound_wsq: the wiki's bound, in its form)
    f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) < N                 (beats_J20: J20's proved BB(20) bound)
    4↑↑341 < N                                            (sigma_lower_bound, the first published bound)

with the standard fast-growing hierarchy below ω³ (f_(ω·(a+1))(n) = f_(ω·a+n)(n), f_(ω²)(n) = f_(ω·n)(n); 4↑↑0 = 1,
4↑↑(n+1) = 4^(4↑↑n)). This is the largest proved bound in the 2-symbol rows here below BB(29). `beats_J20` compares
with J20's proved lower bound, not with an upper bound on J20's σ; the ω² against ω·2 gap settles the real comparison
on paper. Not yet reviewed by the bbchallenge community.

The machine keeps a list of blocks of digits. A level-1 engine runs the first block, and a sweep state carries the
result rightwards, where it decrements, expands or engine-steps the first block that is not all 1s. A marker P walks
through a row of lone 2s, one per phase step. When it reaches the right end, the refill either halts or starts a new
phase with (x − 2)/4 more 2s, depending on the accumulator x mod 4. The machine halts at the sixth refill, at the end
of its third big phase. The proof needs a dominance fact (no block is used up too early), which is formalized as the
invariant `INV` and proved to be preserved by every transition.

- [`0LI0LF_0RJ1RG..._1LH1LU_0LE1LR.md`](0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR.md):
  the write-up (the block rules, the refill, the phases, Lemma D, the residue schedule, the score, verification,
  size, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1, with a new 21-state setup `BB212.v`):
  `halt`, `sigma_lower_bound`, and `BB21_B21_run.abstract_halt` (the abstract machine's halt). About 2 minutes to
  compile; built and probed in CI (job `bb13-bb14`), which requires three closed `Print Assumptions` reports.
- [`verify_w2/`](verify_w2/): the ω² bound (2026-11-08): `halt`, `sigma_lower_bound`, `sigma_lower_bound_wsq3`,
  `sigma_lower_bound_wsq`, `beats_J20`. B21's halting proof, J20's and R18a's proofs are byte-identical copies
  (`share_check.sh`); the new layer is `BB_FGH_wa*.v`, `BB21_B21_qnt*.v`, `BB21_B21_bound.v`, `BB21_B21_w2.v`. Built
  and probed in CI (job `bb13-bb14`), five closed `Print Assumptions` reports.
- [`tools/b21_writeup_chk.py`](tools/b21_writeup_chk.py): an independent simulator that re-checks the write-up's
  rules on concrete instances, the boot and the residue schedule.

Machine by Racheline; analysis, Coq proofs (2026-11-08: halting, then the ω² bound), probe, write-up and packaging by
this project.

W2PR ([`../BB25/`](../BB25/)) is B21 with a mod-8 refill (four more states): it halts after five big phases instead of
three. Its proof reuses seven of the files in `verify/multifile/` unchanged.
