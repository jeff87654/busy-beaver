# BB(5, 3)

## Current entry: 53-Main (Argon)

```
1RB1LC1RA_1LA2LC1RB_1LB1LD2LC_2RE2LD1RA_1RZ2RE1RB
```

Halts from the blank tape (E0 = `1RZ`). Machine-checked, axiom-free, for σ the number of nonzero cells after the
halting write:

    F(F(7)) < σ  and  F(2 ↑^8 3) < σ,   F(n) = 2 ↑^n n       (sigma_exceeds_f_omega2)

that is, 2 ↑^x x < σ with x = 2 ↑^7 7. F is `f_omega` of `BB53_bound.v` (defined there), not the fast-growing
hierarchy's f_ω. In the standard hierarchy (`Ord.v`'s FGH), [`verify_cmp/`](verify_cmp/) proves

    f_ω(f_ω(7)) < σ  and  f_ω(2 ↑^8 3) < σ        (sigma_exceeds_FGH, via FGH_omega_le_home: f_ω(n) ≤ F(n) for n ≥ 4)

and that σ is above the exact σ of the BB(4,3) entry + 1 (`BB53_beats_BB43`, against that entry's Coq upper bound
σ ≤ 4·2 ↑↑↑ 2 ↑↑↑ 2 ↑↑↑ (2^96 + 6) + 18). The exact σ is 2·M + 6 for an explicit M (`M53_final`, not evaluated). The bbchallenge wiki's
Champions page (read 2026-11-13) has no BB(5,3) champion. Not yet reviewed by the bbchallenge community.

53-Main is a 3-symbol version of the Ackermann engine of Kropitz's BB(3,4) champion: two rounds, the second at an
arrow level set by the output of the first, and the parity of the level decides between another round and the halt.

- [`1RB1LC1RA_1LA2LC1RB_1LB1LD2LC_2RE2LD1RA_1RZ2RE1RB.md`](1RB1LC1RA_1LA2LC1RB_1LB1LD2LC_2RE2LD1RA_1RZ2RE1RB.md):
  the write-up (table, the run, the proof, verification, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `bb53_halts`, `reaches_final`,
  `final_halted`, `final_cells_count`, `final_cells_all_nonblank`, `sigma_exceeds_f_omega2`,
  `sigma_beats_official_bb43`, `bb53_new_champion_main`. Built and probed in CI (job `bb53`), which requires 8 closed
  `Print Assumptions` reports.
- [`verify_cmp/`](verify_cmp/): `sigma_exceeds_FGH`, `FGH_omega_le_home`, `fin_fgh_le_knuth`, `BB53_beats_BB43`
  (written here; loads `verify/`, `../BB43/verify/` and a copy of `Ord.v`), CI job `bb53` (5 closed reports).

Found and proved by **Argon** (a Google Gemini model run by the repository owner), 2026-11-09. Re-checked and
packaged here, 2026-11-13.

No superseded entries in this directory.
