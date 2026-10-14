# busy-beaver

[![Coq proofs](https://github.com/jeff87654/busy-beaver/actions/workflows/coq.yml/badge.svg?branch=main)](https://github.com/jeff87654/busy-beaver/actions/workflows/coq.yml)

Busy beaver results, with machine-checked proofs.

## BB8/

`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_1LC0RH_1RG1LF`, an 8-state, 2-symbol machine that halts
from the blank tape with exactly

    sigma = 12 * (2 ↑^37 3) + 59

ones (Knuth up-arrows), hence after more than 2 ↑^37 3 steps. It runs the BB(7) champion's program
(Kropitz 2025, analysed by Ligocki) with 36 digits instead of 12.

- [`BB8/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_1LC0RH_1RG1LF.txt`](BB8/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_1LC0RH_1RG1LF.txt):
  the analysis, in the notation of the wiki page of the BB(7) champion (configurations, low/mid/high
  level rules, bound), and a comparison with that champion.
- [`BB8/verify/`](BB8/verify/): Coq proofs on top of [busycoq](https://github.com/meithecatte/busycoq)
  (`bd2e36f`, Coq 8.20.1): `halt : halts tm c0`, the score lower bounds `2↑^11 2↑^11 3 < N` and
  `2↑^35 2↑^35 3 < N`, and the exact score `N = 12 * (2↑^37 3) + 58` (N counts the ones before the
  final write; score = N + 1). No axioms. See `BB8/verify/README.md` for the compile commands.
- [`BB8/tools/ligocki_notation.py`](BB8/tools/ligocki_notation.py): an independent cell-by-cell
  simulator that extracts the `B(a; b, ..., z)` configurations and rules of both machines.

## BB9/

`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH1RZ`, a 9-state, 2-symbol machine that halts
from the blank tape with exactly

    sigma = 3 * (2 ↑^(6T-33) 8) + (54 T + 26) / 5,      T = 2 ↑^13 3

ones, hence more than 2 ↑^(2 ↑^13 3) 3 (a tower of 2 ↑^13 3 up-arrows; about f_ω(6 · 2 ↑^13 3) in the
fast-growing hierarchy). It runs the BB(7) champion's program to the point where that champion halts,
re-encodes the result as a fresh digit list with 12B−11 digits (2B+4 = 2 ↑^13 3), runs the champion's
program on that list, and halts. It beats the 2024 BB(9) champion of Jacobzheng, whose exact score is
computed in the same proof. A twin with H0 = 0RH has the same score.

- [`BB9/1RB0RA_..._0LH1RZ.txt`](BB9/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH1RZ.txt):
  the analysis (configurations, rules, the four phases of the run, the exact score, the hierarchy value,
  the comparison with the champion).
- [`BB9/verify/`](BB9/verify/): `BB9_record_1RB0RA_selfcontained.v`, ONE Coq file depending only on the
  standard library (busycoq `bd2e36f` inlined, Coq 8.20.1): `halt`, the exact score, the champion's halting
  and exact score, and `new_champion` (score(champion) < score(ours), with a factor-3 margin). No axioms used.
  Check with plain `coqc` in about an hour. `verify/multifile/` has the original development on busycoq,
  including the twin's proof.


## BB10/

`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC` (n1), a 10-state, 2-symbol machine
that halts from the blank tape with more than

    G^N(33) ones,      G(x) = 2 ↑^(x+1) 3,      N = (6T − 19)/7,      T = 2 ↑^37 3

(machine-checked). Also machine-checked, with the standard definitions of the fast-growing hierarchy and
of Graham's number: f_(ω+1)((3T−13)/7 − 2) < sigma < f_(ω+1)(6T), so its level is exactly ω+1, and
sigma > Graham's number. It runs a sibling of the BB(8) record to the point where that machine halts with the value
T, turns T into a countdown of about 0.43 T periods, and in every period re-encodes its latest (astronomical)
value as the length of the list it clears next, so that each period applies one f_ω-sized step; it halts when
the countdown runs out (which happens because T ≡ 2 mod 7). It beats the BB(10) champion of Racheline (2024),
against that champion's Coq-proved exact score. The exact score is also proved, as an explicit recursion of
Knuth arrows.

- [`BB10/1RB0RA_..._0LJ0LI_1RZ0LC.md`](BB10/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC.md):
  the analysis (overview, notation, rules, the full run, the exact score, size analysis, comparisons,
  verification status).
- [`BB10/verify/`](BB10/verify/): Coq proofs on busycoq (`bd2e36f`, Coq 8.20.1): `halt`, the exact score
  (`score_exact`, closed form `score_closed_unfolded`), the lower bound, `beats_champion` against the
  champion's own exact score, the hierarchy level `fgh_level` and `beats_graham`. No axioms. `verify/multifile/compile_clean.sh` rebuilds everything and runs a
  probe that re-checks the transition table entry by entry. `BB10/verify/BB10_n1_selfcontained.v` is the same proof as one
  file that needs only the Coq standard library (`coqc BB10_n1_selfcontained.v`, about 13 minutes).
- [`BB10/tools/bb10_n1_writeup_chk.py`](BB10/tools/bb10_n1_writeup_chk.py): an independent literal simulator
  that re-checks every rule of the analysis on concrete instances.
- [`BB10/screen/`](BB10/screen/): the heuristic candidate screen that found n1 (completion enumerator, mini-follower,
  the cleared-list filter), with its data and a `check.sh` that reproduces part of it. Its verdicts are not claims.

## BB12/

`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RK0LC_0RL---_0RF1RZ` (T12a), a 12-state, 2-symbol
machine that halts from the blank tape with N ones, where (machine-checked, standard fast-growing hierarchy)

    f_(ω+1)(f_(ω+1)(JJ − 2)) ≤ 6N + 11,      JJ = (3T − 13)/7,      T = 2 ↑^37 3.

It is n1 (BB10/) with two more states. It runs n1's whole computation. Where n1 halts, it rebuilds a countdown in
place from n1's final values, runs n1's period loop a second time (about f_ω(w) more f_ω-sized steps, where w is
n1's final depth), and halts at the end of that second round. It beats n1, against n1's Coq-proved exact score. One
transition (K1) is never read.

- [`BB12/1RB0RA_..._0RL---_0RF1RZ.md`](BB12/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RK0LC_0RL---_0RF1RZ.md):
  the analysis (how it works, the run, the score, comparisons, verification status).
- [`BB12/verify/`](BB12/verify/): Coq proofs on busycoq (`bd2e36f`, Coq 8.20.1): `halt`, the lower bounds
  `sigma_lower_bound` and `score_ge_exact`, `beats_n1`, and the hierarchy bound `fgh_lower2`. No axioms.
  `verify/multifile/compile_clean.sh` rebuilds everything (one 2.6 MB file takes most of the time) and runs a probe
  that re-checks the transition table entry by entry.

## ZF/

**254 states (by Mira-Cult, verified here).** Mira-Cult's ([github.com/Mira-Cult/turing-machines](https://github.com/Mira-Cult/turing-machines))
254-state machine `zfc_254.tm` halts from the blank tape iff ZFC is inconsistent. This is proved end to end in Coq
with no axioms, against the same library ZF ([`ZF/m254/`](ZF/m254/)):

    halts tm c0 <-> (ZFc + AC) ⊢TC ⊥      (ZF/m254/coq/e2e/E2E254.v, zf254_halts_iff_ZFC)

**Our own line.** A **335-state**, 2-symbol Turing machine that halts from the blank tape **iff ZFC is inconsistent**. This
is proved end to end in Coq with no axioms, against the ZF of the Coq Library of Undecidability Proofs
(Kirst & Hermes), with and without regularity and choice:

    halts tm c0 <-> (ZFc + Reg + AC) ⊢TC ⊥      (ZF/stdzf_r3/endtoend/335, zf335_halts_iff_ZFC_reg)

The relative consistency of regularity and of choice (Gödel's L) is formalized at the level of
derivations. The folder also has the predecessors, with 393, 361, 354 and 336 states, each with a Coq proof of
`halts tm c0 <-> prov (Wel v0 v0)` on busycoq's TM semantics, with no axioms.
- The 393-state machine is Andrew Wade's current machine (codeberg.org/ajwade/turing_machine_explorer,
  a port of O'Rear's `zf2.nql`).
- The 361-, 354-, 336- and 335-state machines are built with Wade's compiler from a reworked program; 361/354 search the
  same formal system as Wade's (trusted `Logic.v` identical); the 336/335-state machines use a bounded-fiber REP that
  makes POW and UNI redundant (335 also merges two propositional axioms), proved equivalent to standard ZF in
  Coq (`ZF/stdzf_r3/`).

- [`ZF/README.md`](ZF/README.md): history, what has to be trusted, proof structure, credits.
- [`ZF/machines/`](ZF/machines/): the five machines (Wade's `.tm` format).
- [`ZF/verify/`](ZF/verify/): the Coq proofs and `check.py`, which ties the literal table to the `.tm`
  file, builds the proof and checks the statement and its assumptions.
- [`ZF/generator/`](ZF/generator/): rebuilds the 361-, 354-, 336- and 335-state machines byte for byte.
- [`ZF/stdzf/`](ZF/stdzf/): connects O'Rear's system to the standard ZF of the Coq Library of Undecidability
  Proofs (Kirst & Hermes), with and without regularity. For the 354-state machine (and, in [`ZF/stdzf_r3/`](ZF/stdzf_r3/), the 336- and 335-state machines) it proves end to end
  `halts tm c0 <-> ZFc ⊢TC ⊥` (ZF inconsistent), in one build, with no axioms.
- [`ZF/stdzf_r3/`](ZF/stdzf_r3/): the 335/336-state machines end to end, plus `zfc/` (relative consistency
  of AC via Gödel's L) and `regcon/` (relative consistency of regularity). `python3 check.py` rebuilds
  everything from vendored sources.
