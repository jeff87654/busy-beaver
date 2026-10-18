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

`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF` (C04), a 9-state, 2-symbol machine that halts from the
blank tape (it halts in state H reading 1, on the undefined transition H1) with N ones, where (machine-checked, standard
fast-growing hierarchy)

    f_ω(f_ω(465009)) < N = σ,

and N exceeds the exact score of fw2 (below), the previous BB(9) entry, which it supersedes (machine-checked against
fw2's Coq-proved exact score). C04 runs the BB(7) champion's digit-list counter and starts like our earlier BB(9)
record. When the list is used up it rebuilds it (one f_ω-sized step, giving R₂ with 2R₂ + 4 = 2↑^(12B+26) 4, where
2B + 4 = 2↑^13 3), parks a list of 12R₂ − 10 digits, and runs a cascade that is one orbit of the 5-adic map
L → (3L + c)/5 from 36B + 73. Where that orbit ends depends on all base-5 digits of B and cannot be computed, but all
the constants c are even, so the orbit stays odd, and every odd ending clears the parked list (the second f_ω-sized
step) and then halts. On paper (not machine-checked) f_ω(f_ω(12B+26)) < σ < f_ω(f_ω(12B+27)). It does not beat n1
(BB10/), which is at level f_(ω+1). Found in this project's n1f0 search; parity analysis by a Fable agent; Coq proof by
Opus agents (2026-10-17/18).

- [`BB9/1RB0RA_..._1RI---_0RI0RF.md`](BB9/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF.md):
  the analysis (how it works, the run, the score, comparisons, verification status, credit).
- [`BB9/verify_c04/`](BB9/verify_c04/): Coq proofs on busycoq (`bd2e36f`, Coq 8.20.1): `c04_halts`,
  `c04_sigma_lower_bound`, `c04_beats_fw2`, and a probe that re-checks the table against the machine string. No axioms.
  49 files, about 3.2 CPU-hours (about 1 h 40 min on a 4-vCPU CI runner); built in full from scratch and probed in CI.

**Previous entry (2026-10-16, superseded by C04).** `1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA`
(fw2), with σ > f_ω(f_ω(465009)) and an exact score proved as a recursion. fw2 is a digit-list counter of Ackermann type,
with the digit family and the three counting rules of Jacobzheng's 2024 BB(9) champion (13 of its 18 transitions are the
champion's), that rebuilds its list twice. Machine-checked, against each machine's Coq-proved score: fw2 beats our
earlier BB(9) record (below), two later 9-state machines of this project, Jacobzheng's BB(9) champion and Racheline's
2024 BB(10) champion. Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's
Antigravity (2026-10-15); re-checked here. Its Coq files are also used, unchanged, by C04's comparison.

- [`BB9/1RB0RD_..._1RZ1RA.md`](BB9/1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA.md):
  the analysis (how it works, the run, the score, the comparisons, verification status, credit).
- [`BB9/verify_fw2/`](BB9/verify_fw2/): Coq proofs on busycoq (`bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`, `sigma_lower_bound_strong`, and the five comparisons `fw2_beats_*`. No axioms. The halting
  proof and the bounds compile in about a minute and are built and probed in CI; the comparisons, with the proofs of
  the compared machines, take about 1 h 45 min and were checked locally.
- [`BB9/tools/fw2_writeup_chk.py`](BB9/tools/fw2_writeup_chk.py): an independent literal simulator that re-checks
  the rules of the analysis on concrete instances and follows the first 2·10⁸ steps of the run.

**Earlier record (2026-10-07, superseded by fw2).** `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH1RZ`
halts with exactly 3·(2↑^(6T−33) 8) + (54T + 26)/5 ones, T = 2↑^13 3 (about f_ω(6·2↑^13 3)); it beat Jacobzheng's
champion. [Analysis](BB9/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH1RZ.txt),
[`BB9/verify/`](BB9/verify/) (one self-contained Coq file, and the multi-file development with its twin).

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

## BB13/

`1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_0LG1RI_1RE0RH_1LF0RC_1RM0LE_1LA1LE_0LL1LB_0RM1LL_1RZ1RH` (M13), a 13-state, 2-symbol machine
that halts from the blank tape with score σ (the ones on the halted tape, plus 1 for the final write), where
(machine-checked, standard fast-growing hierarchy)

    f_(ω+2)(f_ω(20)) < σ.

Coq also proves the exact score as an explicit recursion. The machine keeps a level p, an accumulator a and two
counters on the tape. An Ackermann-type evaluator computes an f_p-like function of a; two inner-counter steps give an
f_ω step, a full inner countdown an f_(ω+1) step, and one round of the outer counter an f_(ω+2) step. Parity makes the
outer counter odd after its only reload, so it halts after that round. On paper it exceeds T12a (BB12/) and the
published BB(14)–BB(16) lower bounds; it has not been compared with the f_(ω+2)-class BB(17)/BB(18) champions.
Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity (2026-10-14);
re-checked here.

- [`BB13/1LB1LA_..._1RZ1RH.md`](BB13/1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_0LG1RI_1RE0RH_1LF0RC_1RM0LE_1LA1LE_0LL1LB_0RM1LL_1RZ1RH.md):
  the analysis (how it works, the run, the score, comparisons, verification status, how it was found).
- [`BB13/verify/`](BB13/verify/): Coq proofs on busycoq (`bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`, `sigma_lower_bound_strong`. No axioms. About 30 s to compile; built and probed in CI.
- [`BB13/tools/m13_writeup_chk.py`](BB13/tools/m13_writeup_chk.py): an independent literal simulator that re-checks
  every rule of the analysis on concrete instances.
- [`BB13/search/`](BB13/search/): Argon's search programs (unchanged), with what each does and what was re-run.

## BB14/

`1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LN1RF_1LJ0RA_1RA0LH_1LG1LH_1RK0LM_1RZ0LE_0LE0RJ_1LH1LM_0LH0LL_0LG1LN` (M14), a 14-state, 2-symbol
machine that halts from the blank tape with score σ, where (machine-checked, standard fast-growing hierarchy)

    f_(ω+2)(f_(ω+2)(f_(ω+2)(15))) < σ.

Coq also proves the exact score as a recursion. Same architecture as M13 (level stack, accumulator, inner and outer
counter), but the outer counter is reloaded twice, so it halts after the third f_(ω+2) round. It is a compressed
descendant of Jacobzheng's 14-state f_(ω+1) champion (same evaluator, 20 of 28 transitions shared) and is unrelated to
n1/T12a. On paper its lower bound exceeds T12a and the published BB(14)–BB(16) lower bounds; it has not been compared
with the f_(ω+2)-class BB(17)/BB(18) champions. Found and proved by Argon, a Google Gemini model, run by the repository
owner in Google's Antigravity (2026-10-13); re-checked here.

- [`BB14/1RB1RA_..._0LH0LL_0LG1LN.md`](BB14/1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LN1RF_1LJ0RA_1RA0LH_1LG1LH_1RK0LM_1RZ0LE_0LE0RJ_1LH1LM_0LH0LL_0LG1LN.md):
  the analysis (how it works, the run, the score, comparisons, verification status, how it was found).
- [`BB14/verify/`](BB14/verify/): Coq proofs on busycoq (`bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`, `sigma_lower_bound_strong`. No axioms. About 30 s to compile; built and probed in CI.
- [`BB14/tools/m14_writeup_chk.py`](BB14/tools/m14_writeup_chk.py): an independent literal simulator that re-checks
  every rule of the analysis on concrete instances.

## BB43/

`1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD`, the BB(4,3) champion (4 states, 3 symbols; Pavel Kropitz, May 2024,
analysed by hand by Polygon, October 2025). Coq proves, with no axioms, that it halts from the blank tape, that the
final tape is a single block of σ = 4·e₄ + 18 ones, where e₄ is an explicit recursion (three nested cascades of
G(c) = f1^(2c+11)(1), f1(b) = 3·2^(b+4) − 5), and that

    2↑↑↑2↑↑↑2↑↑↑(2^96 − 1) < e₄ ≤ 2↑↑↑2↑↑↑2↑↑↑(2^96 + 6)

(Knuth arrows; 2^96 ≈ 7.92·10²⁸). This implies the wiki's bracket 2↑↑↑2↑↑↑2↑↑↑(7.92·10²⁸) < e₄ < 2↑↑↑2↑↑↑2↑↑↑(7.93·10²⁸),
which Coq also states and proves (`wiki_bracket`). As far as we know this is the first machine-checked proof
of this machine's halting and score.

- [`BB43/1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD.md`](BB43/1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD.md):
  the analysis (notation, the D/D1 families, the rules, the run, the exact score, the bound and the wiki's,
  verification status, credit).
- [`BB43/verify/`](BB43/verify/): Coq proofs on busycoq (`bd2e36f`, Coq 8.20.1): `bb43_halts`, `reaches_final`,
  `final_halted`, `e4_eq`, `sigma_lower`, `e4_bounds`, `wiki_bracket`, `bb43_main`, and a probe that re-checks the table against the machine string. No axioms.
  About two minutes to compile; built and probed in CI.
- [`BB43/tools/bb43_chk.py`](BB43/tools/bb43_chk.py): an independent literal simulator that re-checks the run from
  blank to step 11828, every rule on concrete instances, and the halting tape.

## PA/m238/

The literal 238-state, 2-symbol machine `pa_238.tm` halts from blank tape iff ordinary
classical PA has a finite refutation. The Coq theorem
`P238.e2e.Targets238.pa238_iff_ordinary_proved` composes actual finite proof and
execution transports in both directions, with closed assumptions.

- [`PA/m238/`](PA/m238/): the exact table, proof sources, vendored dependencies,
  provenance and Coq 8.20.1 reproduction instructions. The `pa238` CI job rebuilds
  the dependency closure and checks all declared assumption probes.

## ZF/

**254 states (by Mira-Cult, verified here).** Mira-Cult's ([github.com/Mira-Cult/turing-machines](https://github.com/Mira-Cult/turing-machines))
254-state machine `zfc_254.tm` halts from the blank tape iff ZFC is inconsistent. This is proved end to end in Coq
with no axioms, against the same library ZF ([`ZF/m254/`](ZF/m254/)):

    halts tm c0 <-> (ZFc + AC) ⊢TC ⊥      (ZF/m254/coq/e2e/E2E254.v, zf254_halts_iff_ZFC)

**ZFC + Grothendieck universes, 296 states.** Mira-Cult's program with one new axiom schema, compiled with Wade's
TMBuilder: a 296-state machine that halts from the blank tape iff ZFC + "every set lies in a Grothendieck universe"
is inconsistent (Tarski–Grothendieck strength). Proved end to end in Coq with no axioms ([`ZF/tg296/`](ZF/tg296/)):

    halts tm c0 <-> (ZFc + AC + GU) ⊢TC ⊥      (ZF/tg296/coq/e2e/E2E_TG.v, tg296_halts_iff_ZFCGU)

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
