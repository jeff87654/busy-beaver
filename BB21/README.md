# BB21/: 21 states, 2 symbols

## Current entry: B21 (Racheline's machine)

    0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR

The bbchallenge wiki's BB(21) champion, found by Racheline and listed on the wiki's Champions page with the lower
bound f_(ω²)^2(4↑↑341), marked "Not independently verified" (checked 2026-11-08). Its halting is proved here. Halts
from the blank tape; R0 (`1RZ` in the string) is the halt. It is read on a 0 and writes 1, so σ = N + 1, where N is
the number of ones when R0 is read. Machine-checked, with no axioms:

    halts tm c0                    (halt)
    4↑↑341 < N,   σ = N + 1        (sigma_lower_bound; 4↑↑0 = 1, 4↑↑(n+1) = 4^(4↑↑n))

**The wiki's bound f_(ω²)^2(4↑↑341) is not proved here.** On paper (an argument, not a Coq lemma) the machine is
f_(ω²)-class, far above every other entry below BB(29). But its *proved* bound is below R18a's (BB(18)) and J20's
(BB(20)), so for now BB(21) ≥ BB(20) + 1 is the better proved bound for BB(21).

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
- [`tools/b21_writeup_chk.py`](tools/b21_writeup_chk.py): an independent simulator that re-checks the write-up's
  rules on concrete instances, the boot and the residue schedule.

Machine by Racheline; analysis, Coq proof (2026-11-08), probe, write-up and packaging by this project.
