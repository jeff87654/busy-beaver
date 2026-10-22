# BB9/: 9 states, 2 symbols

## Current entry: C7

    1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA

Halts from the blank tape in state H reading 1 (H1 is undefined: the halt), so σ = N, the number of ones at the halt.
Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_ω(f_ω(f_ω(f_ω(f_ω(2·(2↑^13 3)))))) < σ        (c7_lower5)
    f_ω(f_ω(f_ω(f_ω(f_ω(f_ω(12)))))) < σ           (c7_lower6_12)

Also f_ω⁴(6·(2↑^13 3) + 3) < σ (`c7_lower`, the first bound proved) and f_ω(f_ω(6·(2↑^13 3) + 3)) < σ
(`c7_beats_m8_bound`), where the left side is the Coq upper bound of the BB(8) entry M8 (`m8_bracket`), so C7 beats
M8. No upper bound is proved. C7 does not beat the 10-state n1 ([`../BB10/`](../BB10/)).

- [`1RB0RA_..._0LI---_1LC0RA.md`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA.md): the write-up
  (how it works, the run, the residues, the score, verification status, credit).
- [`verify_c7/`](verify_c7/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1). To check the claims, read
  `c7/Defs.v`, `c7/Statement.v` and the two theorems at the end of `c7/Lower5.v`: `c7_halts`, `c7_lower5`,
  `c7_lower6_12`, `c7_lower`, `c7_beats_m8_bound`, and `c7_table` (the table against a parse of the machine string).
  The proof runs on an auxiliary 11-state machine that simulates C7 and reuses files of `verify_c04/` and
  `verify_f3/` (checked by `port_check.sh`). CI job `bb9-c7` builds it from scratch and requires eight closed
  `Print Assumptions` reports.

C7 is M8 with H0 = 1RG replaced by H0 = 0LI and a new state I = 1LC/0RA. Found by this project's screen of 9-state
extensions of M8 (2026-10-20) and proved in Coq in this project (2026-10-22).

## Superseded entries and proof bases

These stay in place: the first two are proof bases of the current entry and of M8, and fw2's files are reused by
C04's tree.

| machine | entry | superseded by | why its files remain |
|---|---|---|---|
| [`1RB0RA_..._0LI---_0RC1RF`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF.md) (f3_0RC): f_ω(f_ω(6·(2↑^13 3) + 3)) < σ (`f3_beats_m8_bound`) | 2026-10-22, pull request #30 to #32 | C7 | The first 9-state machine proved above M8's upper bound. [`verify_c7/`](verify_c7/) runs on a variant of its auxiliary 11-state machine and reuses its `lib/`, `score/Score.v` and (with one table row changed) `dev/Base.v`; [`verify_f3/`](verify_f3/) is built in CI (job `bb9-f3`). |
| [`1RB0RA_..._1RI---_0RI0RF`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF.md) (C04): f_ω³(12) < σ < f_ω³(13) (`c04_fgh3`), exact score | 2026-10-18 (pull request #24) to 2026-10-19 | M8 (8 states, the same score; [`../BB8/`](../BB8/README.md)) | The proof base of M8 ([`../BB8/verify_m8/`](../BB8/verify_m8/) builds on [`verify_c04/`](verify_c04/)), and of f3_0RC and C7 (ported files, checked). CI job `bb9-c04`. |
| [`1RB0RD_..._1RD1RI_1RZ1RA`](1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA.md) (fw2): f_ω(f_ω(465009)) < σ, exact score | 2026-10-17 (pull request #21) to 2026-10-18 | C04 (`c04_beats_fw2`) | Four of its files are copied into `verify_c04/lib/` (CI checks them byte for byte). [`verify_fw2/`](verify_fw2/): stage 1 in CI (job `bb9-fw2`); stage 2, the comparisons, about 2 h, checked locally. |
| [`1RB0RA_..._0RG0RE_0LH1RZ`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH1RZ.txt) (the 2026-10-07 record): σ = 3·(2↑^(6T−33) 8) + (54T + 26)/5 exactly, T = 2↑^13 3 | 2026-10-07 to 2026-10-17 | fw2 (`fw2_beats_record`) | **Superseded**, kept as published. [`verify/`](verify/) has its Coq proofs (one self-contained file, and the multi-file development with its twin); fw2's stage-2 comparison uses copies of them. Not built in CI. |

## Tools

- [`tools/fw2_writeup_chk.py`](tools/fw2_writeup_chk.py): an independent literal simulator that re-checks the rules
  of fw2's write-up on concrete instances and follows the first 2·10⁸ steps of its run.
