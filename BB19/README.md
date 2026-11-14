# BB19/: 19 states, 2 symbols

## Current entry: J19_sq (Argon, on Jacobzheng's engine)

    1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RS0RK_1LN1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_1RZ1LL

Halts from the blank tape; S0 (`1RZ` in the string) is the halt. It is read on a 0 and writes 1, so σ = N + 1, where
N is the number of ones when S0 is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω·2)(f_(ω·2)(f_5(2))) < N,   σ = N + 1          (sigma_lower_bound)
    f_(ω·2)(2·f_ω^9(35)) < N                           (sigma_lower_bound: J18_w2_C's proved BB(18) bound)
    f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) < N             (sigma_lower_bound: J20's proved BB(20) bound)

and the exact score N = 2(j + 1) + 1 for the j given by the machine's recursion (`score_exact`; not evaluated).

J19_sq runs Jacobzheng's J20 engine and two lists with the expansion and level maps of Argon's J18_w2_C
([`../BB18/`](../BB18/)), and a new four-state refill that can park a **sentinel** (a single 1) behind the outer
list. The outer rounds never reach it; at the next exhaustion the merged block ends next to it, and the refill reads
it. Since the second and the third merged blocks are both ≡ 0 (mod 3), only the sentinel tells them apart: the
second refills, the third halts. So there are three refills and two rounds at level f_(ω·2), where the 18-state
entries have one.

Its proved bound is above BB(18) + 1's (R18c's f_(ω·2)(f_(ω+1)(f_4(2))): on paper; J18_w2_C's: in Coq, the
same theorem), so BB(19) has its own best proved bound again, and it is also above the proved bound of Jacobzheng's
20-state J20. In Coq it is also above both exact scores: σ(J19_sq) = N + 1 > σ(R18c) + 1 (`beats_R18c_exact`,
`beats_R18c_score`) and σ(J19_sq) > σ(J20) (`beats_J20_exact`, `beats_J20_score`). The
20-state J20_cube ([`../BB20/`](../BB20/)) has a higher proved bound. Not yet reviewed by the bbchallenge community.

- [`1LB0LM_1RC1RN..._0RI1LR_1RZ1LL.md`](1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RS0RK_1LN1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_1RZ1LL.md):
  the write-up (the table, the rules, the sentinel refill, the run, the mod-3 invariant, the size, verification,
  comparisons, credit).
- [`verify_j19sq/`](verify_j19sq/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`, and the exact-score comparisons `beats_R18c_exact`, `beats_R18c_score`, `beats_J20_exact`,
  `beats_J20_score` (`BB19_J19sq_cmp.v`, with copies of R18c's and J20's proofs). A few minutes to compile; built and
  probed in CI (job `bb13-bb14`), which requires seven closed `Print Assumptions` reports.

Found and proved by Argon, a Google Gemini model run by the repository owner in Google's Antigravity (2026-11-09), on
Jacobzheng's J19/J20 architecture; re-checked here.

## Previous entry: J19 (Jacobzheng's machine)

    1RQ1RL_0LI1RC_0LD1LF_0RA1LD_1RB1RE_1LH0LG_1LF1LG_1RE1RM_1LJ1LI_0LK1LI_1RL1RA_0RL0RE_0LN1RM_1LO0LO_1RE1LP_1LN1LN_1LR1RQ_1RZ1LS_0LE0LR

The bbchallenge wiki's BB(19) champion, found by Jacobzheng and listed on the wiki's Champions page with the lower
bound f_(ω+7)^2(5), marked "Not independently verified" (checked 2026-11-07). Proved here. Halts from the blank tape;
R0 (`1RZ` in the string) is the halt. It is read on a 0 and writes 1, so σ = N + 1, where N is the number of ones
when R0 is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+7)(f_(ω+7)(5)) < N,   σ = N + 1        (sigma_lower_bound)

and the exact score 2N = T_8(2) + 23 for the machine's explicit recursion T (`score_exact`; not evaluated). That is
the wiki's claim, exactly.

The machine keeps a list of digits (the outer list) that one sweep engine runs in "marker mode", where a digit at
depth p is f_(ω+p)-class. When it lowers the digit next to the head, the head is expanded into an inner list, which
the same engine runs as an f_ω-class computation. When the outer list
is used up, a refill rebuilds it from the merged block of M ones if M is odd, and halts if M is even. From the boot
list [2, 2] the first refill gives [2, 1^8, 2], whose last digit is cleared at depth 8; the second exhaustion has M
even, because every outer clearing value T_(p+1)(a) is odd, so the machine halts there.

On paper (an argument, not a Coq lemma): far above the two earlier 19-state machines below (Argon's, not records) and
the BB(18) entries. No proved upper bound; not yet reviewed by the bbchallenge community.

In Coq, the 18-state R18a ([`../BB18/`](../BB18/), derived from Jacobzheng's J20) has a proved bound above J19's
(`beats_J19`: f_(ω+7)(f_(ω+7)(5)) < σ(R18a)), so BB(19) ≥ BB(18) + 1 is the better proved bound for BB(19).
From 2026-11-08 the BB(18) entry was Argon's J18_w2_C, above R18a in Coq (`beats_R18a`), so BB(19) ≥ BB(18) + 1 >
f_(ω·2)(2·f_ω^9(35)); since 2026-11-13 BB(19) has its own entry again, J19_sq (above). Argon's 19-state J19_w2 (proved f_(ω·2)(2·f_ω(f_2(15))) < N) is below R18a's proved bound
and is not listed.

- [`1RQ1RL_0LI1RC..._1RZ1LS_0LE0LR.md`](1RQ1RL_0LI1RC_0LD1LF_0RA1LD_1RB1RE_1LH0LG_1LF1LG_1RE1RM_1LJ1LI_0LK1LI_1RL1RA_0RL0RE_0LN1RM_1LO0LO_1RE1LP_1LN1LN_1LR1RQ_1RZ1LS_0LE0LR.md):
  the write-up (the sweep, the two modes, the expansion, the outer rounds, the refill, the run, parity, the score,
  verification, comparisons, credit).
- [`verify_jz19/`](verify_jz19/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`. About 25 s to compile; built and probed in CI (job `bb13-bb14`), which requires three closed
  `Print Assumptions` reports.
- [`tools/j19_writeup_chk.py`](tools/j19_writeup_chk.py): an independent simulator that re-checks the write-up's
  rules on concrete instances.

Machine by Jacobzheng; analysis, Coq proof (2026-11-04), probe, write-up and packaging by this project.

## Earlier entries: M19_fw4_A and M19_fw4 (not records)

These two machines (by Argon, see below) were published here before J19 was proved. Both are far below J19. They are
kept as they were published, with their complete Coq proofs. (Earlier versions of this page said the wiki's BB(19) row was
empty; corrected 2026-11-04.)

### M19_fw4_A

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

### M19_fw4

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
