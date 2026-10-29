# BB7/: 7 states, 2 symbols

## Current entry: champ_231 and its twin champ_232

    1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB      (champ_231)
    1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_1LC0RB      (champ_232, G0 = 1LC)

A digit-list counter of the same family as the BB(7) champion `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_0RG0RF`
(Pavel Kropitz, May 2025; analysis by Shawn Ligocki), with 20 digits instead of 12 and an accumulator that triples
instead of doubling. Machine-checked, with no axioms, for both machines: the machine halts from the blank tape
(`c231_halts`), every halting configuration reached from the blank tape holds exactly σ = 2·W 20 5 + 7 ones, where W is
an explicit recursion (`c231_score`), and

    3↑^20 3 < σ                                   (c231_lower)
    3·(2↑^13 3) + 22 < σ,  2↑^11 (2↑^11 3) < σ   (c231_beats_bb7_champion)

The two numbers on the second line are the BB(7) champion's score by our analysis and the bbchallenge wiki's lower
bound for it. Not yet reviewed by the bbchallenge community.

- [`1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB.md`](1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB.md): the
  write-up (the configurations and rules, the run, the exact score, the bounds, a side-by-side comparison with
  Ligocki's analysis of the champion, champ_232, the Coq proof, verification status, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1). Read `Defs.v` and `Statement.v`. About 25
  minutes to compile (two start-up files take most of it); built and probed in CI (job `bb7`), which requires six
  closed `Print Assumptions` reports from each of `probe231.v` and `probe232.v`.
- [`tools/c231_chk.py`](tools/c231_chk.py): an independent literal simulator that re-checks the start, the rules
  D / Bk / E with their exact step counts on a grid, the halting ones count and the preconditions, for both machines.

The machines were found by Argon (a Google Gemini model run by the repository owner) in this project's scan of the
bbchallenge BB(7) holdout list; the checks, the Coq proof and the write-up are this project's (2026-10-22).

## Decided holdouts

[`holdouts/`](holdouts/README.md): five machines from the bbchallenge BB(7) holdout list proved in Coq never to halt
(`~ halts tm c0`, no axioms): `1RB1LD_1RC0RF_0LA0RA_0LA0LE_1LA0LG_0LA---_1RD1LG`,
`1RB0RC_1RC0RA_1LD0LB_1LE0LA_0LF---_1RC0LG_1LF1LA`, `1RB1RE_1LC0RA_1RF0RD_1LC0LE_1LD0LC_1RG0RE_0RB---`,
`1RB1RE_1RC1RA_0LD1LE_1RE1LE_0RG0RF_---0LG_1LC1RA` and `1RB1RF_0LC1LD_1RD1LD_0RE0RG_1LB1RF_1RA1RD_---0LE`. Each has a
short argument in the README; `holdouts/verify/check.py` checks them (CI job `bb7-holdouts`).

No superseded entries in this directory.
