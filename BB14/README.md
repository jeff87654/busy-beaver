# BB14/: 14 states, 2 symbols

## Current entry: M14d_18

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LN1LK_1RZ0LH_0LG1LJ

Halts from the blank tape; M0 (`1RZ` in the string) is the halt, so σ = N + 1, where N is the number of ones when M0
is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+2)^17(f_(ω+1)(f_(ω+1)(3))) < N,   σ = N + 1        (sigma_bound_fw1)
    f_(ω+2)^18(f_ω(f_ω(3))) < N                             (sigma_bound)

and the exact score N = p + a + 5 for the explicit pair (p, a) = `pa19` (`score_exact`; not evaluated).

M14d_18 is M13b ([`../BB13/`](../BB13/)) with L0 sent to a new state N (`0LG1LJ`). N ends the left walk that
starts both kinds of round: in a D round it hands over to the engine one level cell further left, and a reload now
always restarts at one large fixed configuration (above f_ω(f_ω(3))), which is also where the 160-step opening lands. The
level p, known modulo 3^13, picks each round; the run makes 13 reloads and 5 D rounds, eighteen f_(ω+2) rounds in
all, before p lands in the halting class.

On paper (an argument, not a Coq lemma), its proved lower bound is above M14b's (below) and above the proved lower
bounds of both 16-state entries, M16_B and M16_C ([`../BB16/`](../BB16/)); it is below the 17-state entry M17_B's
f_(ω+3)-class bound. None of these has a proved upper bound. Not yet reviewed by the bbchallenge community.

- [`1RB1RA_1RI1RC..._1RZ0LH_0LG1LJ.md`](1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LN1LK_1RZ0LH_0LG1LJ.md): the write-up (how it works, the run, the score, verification, comparisons).
- [`verify_m14d/`](verify_m14d/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_bound`, `sigma_bound_fw1`. About 35 s to compile; built and probed in CI (job `bb13-bb14`), which requires
  four closed `Print Assumptions` reports.
- [`tools/m14d_writeup_chk.py`](tools/m14d_writeup_chk.py): an independent literal simulator that re-checks the
  rules of the write-up on concrete instances and re-derives the order of the rounds from the closed form of W.

Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity (2026-11-03);
re-checked here.

## Previous entry: M14b

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LN0LL_0LH1LK_1RZ0LH_0RJ0LI

Halts from the blank tape; M0 (`1RZ` in the string) is the halt, so σ = N + 1, where N is the number of ones when M0
is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+2)^9(f_(ω+1)(f_(ω+1)(3))) < N + 1 = σ        (sigma_lower_bound)

and the exact score N = p + a + 5 for the explicit pair (p, a) = `pa13` (`score_exact`; not evaluated).

M14b is M13b ([`../BB13/`](../BB13/)) with one more state, N, which splits each reload by the parity of the
level. The even branch restarts the opening round at a high level instead of making tokens, which gives nine
f_(ω+2) rounds instead of six. On paper, its proved lower bound exceeds M14's (below) and the BB(14)–BB(16) lower
bounds published when it was added; M14d_18's (above) exceeds it.

- [`1RB1RA_1RI1RC..._1RZ0LH_0RJ0LI.md`](1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LN0LL_0LH1LK_1RZ0LH_0RJ0LI.md): the write-up (how it works, the run, the score, verification, relation to other entries).
- [`verify_m14b/`](verify_m14b/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`. About 40 s to compile; built and probed in CI (job `bb13-bb14`), which requires three closed
  `Print Assumptions` reports.
- [`m13b_m14b_writeup_chk.py`](../BB13/tools/m13b_m14b_writeup_chk.py): an independent literal simulator that re-checks every rule of the
  write-up on concrete instances (shared by M13b and M14b).

Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity (2026-10-28);
re-checked here.

## Older entry: M14

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LN1RF_1LJ0RA_1RA0LH_1LG1LH_1RK0LM_1RZ0LE_0LE0RJ_1LH1LM_0LH0LL_0LG1LN

Halts from the blank tape; J0 (`1RZ` in the string) is the halt, so σ = N + 1, where N is the number of ones when J0
is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+2)(f_(ω+2)(f_(ω+2)(15))) < N + 1 = σ        (sigma_lower_bound)

and the stronger f_(ω+2)(f_(ω+2)(f_(ω+1)^15(f_ω(21)))) < σ (`sigma_lower_bound_strong`); the exact score is an
explicit recursion (`score_exact`; not evaluated). On paper (not machine-checked), this proved lower bound exceeds
T12a's and the published lower bounds for BB(14)–BB(16); it has not been compared with the f_(ω+2)-class
BB(17)/BB(18) champions.

- [`1RB1RA_..._0LH0LL_0LG1LN.md`](1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LN1RF_1LJ0RA_1RA0LH_1LG1LH_1RK0LM_1RZ0LE_0LE0RJ_1LH1LM_0LH0LL_0LG1LN.md):
  the write-up (how it works, the run, the score, comparisons, verification status, how it was found).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`, `sigma_lower_bound`,
  `sigma_lower_bound_strong`. About 30 s to compile; built and probed in CI (job `bb13-bb14`), which requires four
  closed `Print Assumptions` reports.
- [`tools/m14_writeup_chk.py`](tools/m14_writeup_chk.py): an independent literal simulator that re-checks every
  rule of the write-up on concrete instances.

Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity (2026-10-13);
re-checked here. M14 is a compressed descendant of Jacobzheng's 14-state f_(ω+1) champion (same evaluator, 20 of 28
transitions shared). Same architecture as M13 ([`../BB13/`](../BB13/)), with the outer counter reloaded twice.
