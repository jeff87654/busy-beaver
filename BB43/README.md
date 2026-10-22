# BB43/: 4 states, 3 symbols

## Current entry: the BB(4,3) champion

    1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD

Found by Pavel Kropitz (May 2024) and analysed by hand by Polygon (October 2025); this directory has a Coq proof of
that analysis. Machine-checked, with no axioms: the machine halts from the blank tape (`bb43_halts`), the final tape
is a single block of σ = 4·e₄ + 18 ones, where e₄ is an explicit recursion (`reaches_final`, `final_halted`,
`e4_eq`, `bb43_main`), and

    2↑↑↑2↑↑↑2↑↑↑(2^96 − 1) < e₄ ≤ 2↑↑↑2↑↑↑2↑↑↑(2^96 + 6)        (e4_bounds)

which implies the bbchallenge wiki's bracket 2↑↑↑2↑↑↑2↑↑↑(7.92·10²⁸) < e₄ < 2↑↑↑2↑↑↑2↑↑↑(7.93·10²⁸) (`wiki_bracket`).

- [`1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD.md`](1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD.md): the write-up
  (notation, the rules, the run, the exact score, the bound and the wiki's, verification status, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `bb43_halts`, `reaches_final`,
  `final_halted`, `e4_eq`, `sigma_lower`, `e4_bounds`, `wiki_bracket`, `bb43_main`, and a probe that re-checks the
  table against the machine string. About two minutes to compile; built and probed in CI (job `bb43`), which
  requires thirteen closed `Print Assumptions` reports.
- [`tools/bb43_chk.py`](tools/bb43_chk.py): an independent literal simulator that re-checks the run from blank to
  step 11828, every rule on concrete instances, and the halting tape.

The Coq proof, the simulator and the write-up are this project's (2026-10-17).

No superseded entries in this directory.
