# BB9/: 9 states, 2 symbols

## Current entry: h003

    1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC

Halts from the blank tape in state H reading 1 (H1 is undefined: the halt), so σ = N, the number of ones at the halt.
Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_ω(f_ω(f_ω(f_ω(f_ω(f_ω(f_ω(12))))))) < σ              (h003_lower7_12)
    f_ω(f_ω(f_ω(f_ω(f_ω(f_ω(6·(2↑^13 3) + 2)))))) < σ        (h003_lower)

Also f_ω(f_ω(6·(2↑^13 3) + 3)) < σ (`h003_beats_m8_bound`), where the left side is the Coq upper bound of the BB(8)
entry M8 (`m8_bracket`), so h003 beats M8. Its proved bound is one f_ω above C7's (f_ω⁶(12)); on paper σ(h003) >
f_ω(σ(C7)) (the write-up, section 2.3). No upper bound is proved. h003 does not beat the 10-state n1
([`../BB10/`](../BB10/)).

- [`1RB0RA_..._0LI---_1RI1RC.md`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC.md): the write-up
  (how it works, the tops, the residues, the exit into M8's endgame, the score, verification status, credit).
- [`verify_h003/`](verify_h003/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1). To check the claims, read
  `h003/Defs.v` and `h003/Statement.v`: `h003_halts`, `h003_lower7_12`, `h003_lower`, `h003_beats_m8_bound`, and
  `h003_table` (the table against a parse of the machine string). The proof runs on an auxiliary 11-state machine that
  simulates h003 and reuses C04's cascade and endgame unchanged, with files of `verify_c04/`, `verify_f3/` and
  `verify_c7/` (checked by `port_check.sh`). CI job `bb9-h003` builds it from scratch and requires six closed
  `Print Assumptions` reports.

h003 is M8 with E0 = 1LH replaced by E0 = 0LH, H0 = 1RG replaced by H0 = 0LI, and a new state I = 1RI/1RC. Found by
re-screening this project's set of 9-state extensions of M8 in residue-faithful worlds, and proved in Coq in this
project (2026-10-22).

## Superseded entries and proof bases

These stay in place: C7, f3_0RC and C04 are proof bases of the current entry (and C04 of M8), and fw2's files are
reused by C04's tree.

| machine | entry | superseded by | why its files remain |
|---|---|---|---|
| [`1RB0RA_..._0LI---_1LC0RA`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA.md) (C7): f_ω⁶(12) < σ and f_ω⁵(2·(2↑^13 3)) < σ (`c7_lower6_12`, `c7_lower5`) | 2026-10-22 (pull request #32) | h003 (one f_ω higher) | [`verify_h003/`](verify_h003/) reuses five of its files (`Res.v`, `KStep.v`, `Ones.v`, `G_pbab.v`, `G_pbc.v`, checked) and ports its `dev/Base.v` (h003's table rows) and `c7/Sim.v`; [`verify_c7/`](verify_c7/) is built in CI (job `bb9-c7`). |
| [`1RB0RA_..._0LI---_0RC1RF`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF.md) (f3_0RC): f_ω(f_ω(6·(2↑^13 3) + 3)) < σ (`f3_beats_m8_bound`) | 2026-10-22, pull request #30 to #32 | C7 | The first 9-state machine proved above M8's upper bound. [`verify_c7/`](verify_c7/) and [`verify_h003/`](verify_h003/) run on variants of its auxiliary 11-state machine; `verify_h003/` reuses 38 of its files (33 byte-identical, 5 with the halting tape changed) and `verify_c7/` its `lib/`, `score/Score.v` and (with one table row changed) `dev/Base.v`; [`verify_f3/`](verify_f3/) is built in CI (job `bb9-f3`). |
| [`1RB0RA_..._1RI---_0RI0RF`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF.md) (C04): f_ω³(12) < σ < f_ω³(13) (`c04_fgh3`), exact score | 2026-10-18 (pull request #24) to 2026-10-19 | M8 (8 states, the same score; [`../BB8/`](../BB8/README.md)) | The proof base of M8 ([`../BB8/verify_m8/`](../BB8/verify_m8/) builds on [`verify_c04/`](verify_c04/)), and of f3_0RC, C7 and h003 (ported files, checked). CI job `bb9-c04`. |
| [`1RB0RD_..._1RD1RI_1RZ1RA`](1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA.md) (fw2): f_ω(f_ω(465009)) < σ, exact score | 2026-10-17 (pull request #21) to 2026-10-18 | C04 (`c04_beats_fw2`) | Four of its files are copied into `verify_c04/lib/` (CI checks them byte for byte). [`verify_fw2/`](verify_fw2/): stage 1 in CI (job `bb9-fw2`); stage 2, the comparisons, about 2 h, checked locally. |
| [`1RB0RA_..._0RG0RE_0LH1RZ`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH1RZ.txt) (the 2026-10-07 record): σ = 3·(2↑^(6T−33) 8) + (54T + 26)/5 exactly, T = 2↑^13 3 | 2026-10-07 to 2026-10-17 | fw2 (`fw2_beats_record`) | **Superseded**, kept as published. [`verify/`](verify/) has its Coq proofs (one self-contained file, and the multi-file development with its twin); fw2's stage-2 comparison uses copies of them. Not built in CI. |

## Tools

- [`tools/fw2_writeup_chk.py`](tools/fw2_writeup_chk.py): an independent literal simulator that re-checks the rules
  of fw2's write-up on concrete instances and follows the first 2·10⁸ steps of its run.
