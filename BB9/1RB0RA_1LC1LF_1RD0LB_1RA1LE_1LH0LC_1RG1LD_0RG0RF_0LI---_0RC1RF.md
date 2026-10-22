# f3_0RC: a 9-state machine above M8's Coq upper bound

    1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF

Below we call this machine **f3_0RC** (its label in the screen that found it, section 5). It halts from the blank tape,
and Coq proves, with no axioms and with the standard fast-growing hierarchy, that its score σ satisfies

    f_ω(f_ω(6·(2↑^13 3) + 3)) < σ        (f3_beats_m8_bound)

The left side is the Coq upper bound of the BB(8) entry M8
([`../BB8/1RB0RA_..._0RG0RF_1RG---.md`](../BB8/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---.md)):
σ(M8) < f_ω(f_ω(6·(2↑^13 3) + 3)) (`m8_bracket`). So f3_0RC beats M8. M8's exact score depends on where its cascade
ends, which cannot be computed, and the comparison holds in every case. More precisely, Coq proves
f_ω(f_ω(12R'' + 10)) < σ (`f3_lower`), where 2R'' + 4 is an explicit iterate of Knuth arrows, about 2↑^7(2↑^13 3).

The gain is modest. f3_0RC is at M8's level of the hierarchy: on paper, f_ω(f_ω(f_ω(12))) < σ < f_ω(f_ω(f_ω(13))),
like M8. Only the lower half of that bracket follows from Coq results (section 2.2). What is proved is that σ is above
M8's Coq upper bound. Written 2026-10-21.

**Dominated (2026-10-22)** by C7 ([`1RB0RA_..._0LI---_1LC0RA.md`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA.md)),
whose Coq lower bound f_ω⁴(6·(2↑^13 3) + 3) is two applications of f_ω above M8's upper bound. C7's proof is built on
this one's auxiliary machine.

f3_0RC was the first 9-state entry that beats M8 in every endgame class (the BB(9) entry from pull request #30 until
pull request #32, both 2026-10-22). C7 is proved on the same proof infrastructure (this development's auxiliary machine
X), and its Coq lower bound is now f_ω⁶(12) < σ (`c7_lower6_12`). The current BB(9) entry is listed in
[`README.md`](README.md).

f3_0RC runs M8's engine and differs from M8 only in state H and in a new state I. M8's H0 = 1RG becomes H0 = 0LI, a look
at the cell left of H. If that cell holds a 1, I1 = 1RF and F0 = 1RG redo M8's H0 in three steps. If it is blank, which
happens only at the two top-level exhaustions, I0 = 0RC does something new: it rebuilds a much longer digit list. After
that, the run is M8's cascade and endgame, with a larger parked list.

|   | 0   | 1   |                                         |
|---|-----|-----|-----------------------------------------|
| A | 1RB | 0RA |                                         |
| B | 1LC | 1LF |                                         |
| C | 1RD | 0LB |                                         |
| D | 1RA | 1LE |                                         |
| E | 1LH | 0LC |                                         |
| F | 1RG | 1LD |                                         |
| G | 0RG | 0RF |                                         |
| H | 0LI | --- | H1 is undefined: the halt               |
| I | 0RC | 1RF | I0 is read only at top-level exhaustions |

**Main facts.** N is the number of 1s on the tape when the machine is in state H reading 1. The cell under the head
already holds a 1, so whatever 1 the halting transition is taken to write (the usual convention is 1RZ), σ = N.

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `f3_halts : halts tm3 c0`. |
| Score | **f_ω(f_ω(6·(2↑^13 3) + 3)) < σ**, machine-checked (`f3_beats_m8_bound`). |
| More precisely | f_ω(f_ω(12R'' + 10)) < σ with 2R'' + 4 = iter (2↑^13 3 − 5) (2↑^6) (iter 4 (2↑^5) 4), machine-checked (`f3_lower`, written without R'' in `Statement.v`). |
| Level | f_ω(f_ω(f_ω(12))) < σ < f_ω(f_ω(f_ω(13))), M8's level. The lower half follows from Coq results; the upper half is on paper (section 2.2). |
| M8 (the BB(8) entry, `../BB8/`) | **Beaten**, machine-checked through M8's Coq upper bound: σ(M8) < f_ω(f_ω(6·(2↑^13 3) + 3)) < σ (`m8_bracket` there, `f3_beats_m8_bound` here). This holds whichever of M8's endgame classes its run is in. |
| C04 (`1RB0RA_..._1RI---_0RI0RF`, this folder) | Beaten: it has M8's score. |
| fw2 and the machines it beats (this folder) | Beaten, through M8 (`m8_beats_fw2`). |
| n1 (`../BB10/`, f_(ω+1)) | **Not** beaten. |
| Steps | Not computed. |

---

## 1. How it works

### 1.1 Relation to M8

M8 = `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---` and f3_0RC agree on states A–G and on H1, the halt. M8's
H0 = 1RG writes a 1 and moves right into G. f3_0RC's H0 = 0LI writes 0 and moves left into I instead.

- If the cell left of H holds a 1, I1 = 1RF keeps it and moves back right in F, reading the 0 that H just wrote. F0 = 1RG
  writes the 1 and moves right into G. This is M8's H0 step, done in three steps.
- If the cell left of H is blank, I0 = 0RC moves back right in C, and the run leaves M8's.

M8 reads H0 right after E0, that is, at an exhaustion: the digit list is used up. In our simulations of M8's run, the
cell left of H is blank at exactly two H0 events, the two top-level exhaustions, where nothing lies left of the list. At
every other exhaustion (the cascade's, with tokens to the left) it holds a 1. So f3_0RC changes M8 only at the two
top-level exhaustions. The Coq proof does not rely on this observation: it follows f3_0RC's own run (section 3).

### 1.2 The run

The notation is that of C04's write-up
([`1RB0RA_..._1RI---_0RI0RF.md`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF.md), section 1.1):
Kt(list; m; r; t) is the digit-list counter of the BB(7) champion, and U_j is the clear of a list of depth j, with
2·U_j(x) + 4 = 2↑^(j+1)(2x + 4). B is C04's and M8's counter, with 2B + 4 = 2↑^13 3.

- **P0, start.** As in M8, the blank tape reaches Kt(1^11; 1; 3B + 2; 0), where the digit list is used up for the first
  time.
- **P1, exhaustion #1 (top level, I0).** M8 rebuilds a list of 12B + 25 digits here. f3_0RC instead writes a short
  list with two non-zero digits, 4 and 2B − 1 (`XREB1`, parametric in B). Clearing them gives the accumulator
  R'' = U_5^(2B−1)(U_4^4(0)), so 2R'' + 4 = iter (2↑^13 3 − 5) (2↑^6) (iter 4 (2↑^5) 4), about 2↑^7(2↑^13 3)
  (`Rpp_explicit`).
- **P2, a rebuild without E0.** The champion's rules turn R'' into a list of 12R'' + 10 zero digits and a digit 2
  (`XREB2`, parametric in R''). Clearing it gives R₂′ with 2R₂′ + 4 = 2↑^(12R''+12) 4 (on paper; in Coq,
  R₂′ = U_(12R''+10)(U_(12R''+10)(0))). This is the first f_ω-sized step. M8's corresponding value has 12B + 26 in
  place of 12R'' + 12.
- **P3, exhaustion #2 (top level, I0).** The list is used up again with R₂′ as the accumulator. This top-level
  exhaustion parks a list of about 12R₂′ zero digits and starts a cascade run (`XTOPENTRY`), takes one cascade sub-step
  with r = 3 (`XTOP1`), and stops (L ≡ 0 mod 5). The cascade then starts at L₀′ = (324R'' − 359)/25.
- **P4, M8's cascade and endgame.** From there the run is M8's (and C04's) cascade: one orbit of the 5-adic map
  L → (3L + c)/5, whose constants are all even, so the orbit stays odd. It enters one of the keys 31, 37, 43, 49, 55, and
  then the class-b ending clears the parked list (the second f_ω-sized step) and halts on H1. See sections 1.4–1.6 of
  C04's write-up.

### 1.3 Residues

The halt needs the cascade start to be odd and ≡ 1 (mod 3), as in C04. Here this follows from the residues of the
accumulators, whatever B is. Every accumulator made by a clear of depth j ≥ 1 has 2R + 4 = 2^(2^(2^h)) with h ≥ 2,
which is 36 mod 100. So R ≡ 16 (mod 50) (`U_mod50`, `Rpp_mod50`). With R'' = 50q + 16, the exhaustion-#2 run (in the sketch notation, L = 36R'' + 37) is
≡ 3 (mod 5), its one sub-step lands on a multiple of 5 (the stop), and L₀′ = 648q + 193 is odd and ≡ 1 (mod 3)
(`x_vals`, `L1x_props`). B enters only through the digit 2B − 1 of P1, so its residues play no role.

---

## 2. The score

### 2.1 What Coq proves

The files to read are [`verify_f3/f3/Defs.v`](verify_f3/f3/Defs.v) and
[`verify_f3/f3/Statement.v`](verify_f3/f3/Statement.v), with busycoq's `TM.v`. `Defs.v` defines `tm3`, `ones`, `iter`,
`arrow`, `f` and `f_omega` (from the ones count on, the same text as M8's `Defs.v`). `Statement.v` states the results in
those terms and busycoq's (`halts`, `halted`, `c0`, `-[ ]->*`):

    Statement.f3_table          : String.length f3_string = 62 /\
                                  forall q s, tm3 (q, s) = parse_slot f3_string (st_idx q) (sym_idx s)
    Statement.f3_halts          : halts tm3 c0
    Statement.f3_lower          : forall c N, c0 -[ tm3 ]->* c -> halted tm3 c -> ones c N ->
                                    f_omega (f_omega (6 * iter (arrow 13 2 3 - 5) (arrow 6 2) (iter 4 (arrow 5 2) 4) - 14)) < N
    Statement.f3_beats_m8_bound : forall c N, c0 -[ tm3 ]->* c -> halted tm3 c -> ones c N ->
                                    f_omega (f_omega (6 * arrow 13 2 3 + 3)) < N

In `f3_lower`, 6 · iter (…) − 14 = 6 · (2R'' + 4) − 14 = 12R'' + 10. `f3_beats_m8_bound` follows from it by
`Final3.m8_le` (6 · 2↑^13 3 + 3 ≤ 12R'' + 10). The comparison with M8 is the chain of two theorems:

    BB8/verify_m8  Statement.m8_bracket        : ... -> ... /\ N8 < f_omega (f_omega (6 * arrow 13 2 3 + 3))
    BB9/verify_f3  Statement.f3_beats_m8_bound : ... -> f_omega (f_omega (6 * arrow 13 2 3 + 3)) < N

The two `Defs.v` define `f_omega` and `arrow` with the same text (CI checks it by `diff`). The development where the
proof was written also composed the two in Coq (`f3_beats_m8`, `f3_beats_c04`), against a byte-identical compiled build
of the C04 and M8 trees. That file is not in the repository, because building it here would put the C04 tree, BB8/verify,
BB8/verify_m8 and this tree in one CI job.

### 2.2 How large

M8's score lies between f_ω(f_ω(12B + 26)) and f_ω(f_ω(12B + 27)), with 12B + 26 = 6·(2↑^13 3) + 2. f3_0RC's lies above
f_ω(f_ω(12R'' + 10)), with 12R'' + 10 about 6·2↑^7(2↑^13 3). Both inner arguments lie between f_ω(12) and f_ω(13).
For M8 this is C04's `Bx_fw`. For f3_0RC, 2R'' + 4 < 2↑^12 5 < f_13(13) = f_ω(13), on paper. So f3_0RC is at M8's level:

- f_ω(f_ω(f_ω(12))) < σ follows from Coq results: f_ω(12) < 12B + 26 (`Bx_fw`), f_ω is increasing, and
  `f3_beats_m8_bound`. It is not stated as one Coq theorem.
- σ < f_ω(f_ω(f_ω(13))) is on paper. The same analysis as C04's upper bound gives, on paper, σ < f_ω(f_ω(12R'' + 13)), and
  12R'' + 13 < f_ω(13). There is no Coq upper bound for f3_0RC.

The improvement over M8 is in the inner argument of f_ω(f_ω(·)): about 2↑^7(2↑^13 3) instead of 6·(2↑^13 3).

---

## 3. Verification

### 3.1 How the proof is organised

[`verify_f3/`](verify_f3/) holds the development: Coq 8.20.1 on busycoq (commit `bd2e36f`), 51 files and a probe, no
axioms. It reuses C04's development ([`verify_c04/`](verify_c04/)) through an auxiliary 11-state machine X:

    X = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LJ0LC_0RG1LD_0LH1LH_1RI---_0RI0RF_0LK---_0RC1RH

X is C04 with E0 = 1LH replaced by E0 = 1LJ, J = 0LK / halt, K = 0RC / 1RH. When the cell left of H holds a 1, J halts,
as C04 does in H. When it is blank, J0 and K1 = 1RH bring X back to C04's configuration. These are three X steps for
C04's one E0 step, and K0 = 0RC is f3_0RC's I0 = 0RC.

- **Reused C04 lemmas.** `dev/Base.v` redefines the tactic `step` as one C04 step. C04's generated machine lemmas
  (champion rules, cascade sub-steps, stop, entry, class-b tails, the key-31 endgame) then compile unchanged on X. 31
  files are C04's up to mechanical renames, which `port_check.sh` re-applies and CI checks. Five abstract files are
  lightly edited: C04's own top level is removed, and the cascade start is made a parameter.
- **New machine lemmas** (generated by the same symbolic executor, retargeted to X, counting raw X steps): `XREB1`
  (P1, `dev/G_xreb1.v`), `XREB2` (P2, `dev/G_xreb2.v`), `XTOPENTRY` and `XTOP1` (P3, `dev/G_xtop.v`).
- **New abstract files.** `dev/XTop.v` chains P0–P3 on tokens, proves the residues and reaches the cascade (`reach_topX`).
  `dev/XFinal.v` applies C04's cascade and endgame (`x_halts`). `dev/XScore.v` adapts C04's score argument
  (every halting count of X exceeds f_ω(f_ω(12R'' + 10))).
- **Simulation.** `f3/Sim.v` maps f3_0RC's states A..F → A..F, G → I, H → J, I → K, and relates configurations through
  finite tape lists. f3's F0 = 1RG is X's F0, G, H0, and f3's I1 = 1RF is X's K1 followed by H0. f3_0RC halts exactly
  where X does, on the same tape, so its halting and its counts come from X's.
- **Statements.** `f3/Final3.v` proves the theorems; `f3/Statement.v` restates them with `Defs.v` only, and pins the
  table against the machine string through a string parser.

`probe.v` checks the 18 table entries by conversion and against the parser of the literal string, prints `c0`, `tape0`
and the definitions, states the three main results as one conjunction with qualified names (`f3_all_ok`), and runs
`Print Assumptions` five times (the conjunction and each theorem of `Statement.v`). All five report "Closed under the
global context".

### 3.2 Build

`verify_f3/compile_clean.sh` builds everything from scratch, then runs the probe. The GitHub workflow (job `bb9-f3`)
runs it whenever these files change (and weekly). It also runs `port_check.sh`, checks that `lib9/` is byte-identical to
C04's `lib/`, and diffs the definitions of `f3/Defs.v` against M8's `Defs.v`. Timings and the recorded local build are
in [`verify_f3/README.md`](verify_f3/README.md).

### 3.3 Not machine-checked

- **σ = N.** In Coq the halt is the undefined transition H1, and `ones` counts the 1s of the halted configuration.
- **The level,** section 2.2: the upper half, and the composition of the lower half into one statement.
- **The M8 comparison as one theorem.** It is the two theorems of section 2.1 (and was composed in Coq in the
  development).
- **Section 1.1's observation** about M8's H0 events (simulations). The proof follows f3_0RC's own run.

---

## 4. Discovery and credit

- **Found** by this project's screen of 9-state extensions of M8 (2026-10-19): machines with M8's H0 replaced by a look
  to the left (H0 = 0LI, I1 = 1RF) and each choice of I0. Among the 36 choices, I0 = 0RC (and its twin I0 = 1RD) ran
  M8's endgame after a larger second escalation for every tested B. A literal simulator checked the phases P1–P3 for twelve
  values of B from 6 to 3966, and for decoupled values of the accumulators. An independent simulator confirmed them, and that in all nine
  endgame routes of M8 it halts as M8 does. The twin `…_0LI---_1RD1RF` (I0 = 1RD) behaved identically in those runs; it is
  not proved here.
- **Proved** in Coq in this project (2026-10-20), on top of C04's development (section 5 of C04's write-up for its
  credits).
- **Built on** the BB(7) champion of Kropitz (2025; analysed by Ligocki), whose counter it runs, and on C04 and M8,
  whose cascade and endgame it shares.
