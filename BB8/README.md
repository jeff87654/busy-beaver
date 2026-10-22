# BB8/: 8 states, 2 symbols

## Current entry: M8

    1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---

Halts from the blank tape (in state H reading 1, on the undefined transition H1) with score σ, where, machine-checked
with the standard fast-growing hierarchy and no axioms,

    f_ω(f_ω(f_ω(12))) < σ < f_ω(f_ω(f_ω(13)))        (m8_fgh3)

More precisely f_ω(f_ω(6·(2↑^13 3) + 2)) < σ < f_ω(f_ω(6·(2↑^13 3) + 3)) (`m8_bracket`), and
f_(ω+1)(3) < σ < f_(ω+1)(4) (`m8_coarse`); the exact score is an explicit recursion (`m8_score_exact`).

- [`1RB0RA_..._0RG0RF_1RG---.md`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---.md): the write-up (the
  reduction from C04, the run, the score, verification status, credit).
- [`verify_m8/`](verify_m8/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1). To check the claims, read `Defs.v` and
  `Statement.v`: `m8_halts`, `m8_fgh3`, `m8_bracket`, `m8_coarse`, `m8_score_exact`, `m8_beats_bb8`,
  `m8_beats_champ35`, `m8_beats_fw2`, and `m8_table` (the table against the machine string). The proof is built on
  C04's ([`../BB9/verify_c04/`](../BB9/verify_c04/)). CI job `bb8-m8` builds C04's tree, `verify/` and this layer
  from scratch and requires twenty closed `Print Assumptions` reports.

M8 is the BB(7) champion of Kropitz (2025) with its halt E0 redirected to a new state H. It was obtained by reducing
the 9-state machine C04 (two states of C04 do what one transition of M8 does), in this project, 2026-10-18.

## Superseded

| machine | entry | superseded by | why its files remain |
|---|---|---|---|
| `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_1LC0RH_1RG1LF` (champ35): σ = 12·(2↑^37 3) + 59 exactly (Coq) | 2026-10-04 to 2026-10-18 | M8 (`m8_beats_champ35`) | `verify_m8/Beats8.v` loads [`verify/`](verify/) to compare M8 with its exact count; CI job `bb8` builds it. The BB(10) and BB(12) entries begin by running its computation. |

- [`1RB0RA_..._1RG1LF.txt`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_1LC0RH_1RG1LF.txt): its analysis, in the
  notation of the BB(7) champion's wiki page.
- [`verify/`](verify/): its Coq proofs (`halt`, `score_exact`, `sigma_lower_bound`, `sigma_lower_bound_strong`; no
  axioms).

## Tools

- [`tools/ligocki_notation.py`](tools/ligocki_notation.py): a cell-by-cell simulator that extracts the
  `B(a; b, ..., z)` configurations and rules of champ35 and of the BB(7) champion.
