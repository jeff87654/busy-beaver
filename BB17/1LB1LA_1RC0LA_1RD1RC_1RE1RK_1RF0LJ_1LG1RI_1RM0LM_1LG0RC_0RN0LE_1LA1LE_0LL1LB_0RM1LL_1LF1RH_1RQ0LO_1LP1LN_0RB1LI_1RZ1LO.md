# M17_B: a 17-state machine at level f_(ω+3), three rounds

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1LN_0RB1LI_1RZ1LO

|   | 0   | 1   |                                                                  |
|---|-----|-----|------------------------------------------------------------------|
| A | 1LB | 1LA |                                                                  |
| B | 1RC | 0LA |                                                                  |
| C | 1RD | 1RC |                                                                  |
| D | 1RE | 1RK |                                                                  |
| E | 1RF | 0LJ |                                                                  |
| F | 1LG | 1RI |                                                                  |
| G | 1RM | 0LM |                                                                  |
| H | 1LG | 0RC |                                                                  |
| I | 0RN | 0LE |                                                                  |
| J | 1LA | 1LE |                                                                  |
| K | 0LL | 1LB |                                                                  |
| L | 0RM | 1LL |                                                                  |
| M | 1LF | 1RH |                                                                  |
| N | 1RQ | 0LO | N0 starts the sweep (M16_B: `0RO`)                               |
| O | 1LP | 1LN | O1 changed (M16_B: `1RM`)                                        |
| P | 0RB | 1LI | P0 is the left-end bounce (M16_B: `1RZ`, the halt)               |
| Q | 1RZ | 1LO | new: Q0 is the halt                                              |

Rows A–M and the slots N1, O0 and P1 are those of M16_B ([`../BB16/`](../BB16/), the BB(16) entry, also Argon's).

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB17_halt_fw3.halt`. |
| Exact score | Machine-checked formula: N = p + a + 5 ones at the halt, where (p, a) = `pa_final` is given by the recursion of section 2 (`score_exact`). The halt Q0 = `1RZ` is read on a 0, so σ = N + 1 = p + a + 6. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+2)^116(f_(ω+3)^3(9)) < N (`sigma_lower_bound`), so f_(ω+3)^3(9) < N (`sigma_lower_bound_fw3_3`). |
| Comparisons | **Argument, not a Coq lemma** (section 4): above the proved lower bounds of BB18_fw3 (the previous BB(18) entry, f_(ω+2)(f_(ω+3)(114))) and of M16_B (BB(16), f_(ω+2)^10(9)). Not yet reviewed by the bbchallenge community. |
| Steps | Not computed. |

## 1. How it works

### The core (shared with M16_B)

M17_B runs on the same engine as M16_B. Read that write-up ([`../BB16/`](../BB16/)) and the BB18_fw3 write-up
([`../BB18/`](../BB18/)) for the configuration family

    Ce_gen p a c r  =  0^∞ (10)^p 1^(a+2) [E] (10)^c 0 r        (head on the cell after the 1s, state E)

the W hierarchy (W 0 b = b + 3, W (j+1) b = (W j)^(b+1)(2)), the c-counter `Kc` (`CE_EVEN`, f_ω when iterated) and
the Kd1 step (f_(ω+1)). All lemmas are parametric in the tail r, and the engine reads the tail as a program
(write `Ce_gen p a 0 X` as "tail X"):

- `1 1 r` → `r`: one Kd1 step, f_(ω+1) (`Kd1_step_all`);
- `0 r` → `1 r`: one D1 cycle (a reload, then a/2 + 1 Kd1 steps), f_(ω+2) (`D1_cycle_all`);
- `1 0 1 s` → `1 s`: one Kd2 step, f_(ω+2) (`Kd2_step_all`); so `(10)^m 1 s` → `1 s` (`Kd2_loop`);
- `0 1 r` → `r`: one `Kd2_alt_step` = a D1 cycle followed by a Kd1 step, f_(ω+2) (`Kd2_alt_step_all`); so
  `0 (10)^m r` → `0 r` (`Kd2_alt_loop`).

The last rule is the one M17_B adds to M16_B's set. It needs no new transitions: it is two old rules in a row. Like
the other rules, it never reads N0, O1, P0 or Q. It does read N1, O0 and P1: every Kd1 step and every Kd2 step
starts with a short turnaround I0, N1, O0, P1, I1 (as in M16_B), so the loops are not confined to rows A–M (the
literal checker confirms both on small instances).

### The new slots: a sweep and a bounce

In M16_B, a tail starting `1 0 0` sends the machine through N0 into the bridge. In M17_B, N0 instead starts a
sweep to the left end of the tape. With h the head cell of `Ce_gen p a 0 (1 0 0 1 z)`:

- E, F and I run as usual (E writes 1 at h, F crosses the 1 at h + 1, I0 moves on at h + 2), and N0 writes 1 at
  h + 3. Q reads the 1 at h + 4 and leaves it (Q1 = `1LO`).
- O and N then walk left: O1 = `1LN` leaves a 1, N1 = `0LO` clears it, and N0 = `1RQ` writes a 1 and makes a
  one-cell excursion through Q. This turns the cells from h + 4 down to the far end of the 1s into the pattern
  below.
- Over the (10)^p part, P, I, N and O (P1 = `1LI`, I0, N1, O0) move the (10) tokens one cell to the left, and P
  reaches the blank left end and reads 0.

The result, after 4p + a + 14 steps (a even), is

    Ce_gen p a 0 (1 0 0 1 z)  →+  P on the left-end 0, then (10)^p 1 1 0 (10)^(a/2+1) 1 1 1 z      [SWEEP_M17B]

Both numbers of the old configuration are now (10) tokens to the right: p of them for the level, a/2 + 1 for the
accumulator. P0 = `0RB` then bounces. In 156 steps it reaches `Ch 2 1 (0 1 1 0 0 (10) 0 0 r)` (`bounce_156`);
the machine is now in the same cascade as at the end of M16_B's opening (`start_boot`), and a W_2 cascade,
`E_1100` and `CE_EVEN` take it to

    P on the left-end 0, then (10)^3 r  →+  Ce_gen 26 W_21(1) 0 (0 r)                            [P0_bounce]

So the bounce eats three tokens and restarts the engine at the level pa_0 = (26, W_21(1)), the same level that the
opening reaches. The bounce reads P0 once at the start and otherwise only core slots and N1, O0, P1.

### One round

Put together (`Full_Round`, for p ≥ 5 and a ≥ 4 even):

| from tail | what runs | to tail |
|---|---|---|
| `1 0 0 1 z` | sweep, bounce | `0 (10)^(p−3) 1 1 0 (10)^(a/2+1) 1 1 1 z` at level pa_0 |
| `0 (10)^(p−3) …` | p − 3 alt steps (`Kd2_alt_loop`) | `0 1 1 0 (10)^(a/2+1) 1 1 1 z` |
| `0 1 …` | one more alt step (`Kd2_alt_step_all`) | `1 0 (10)^(a/2+1) 1 1 1 z` = `(10)^(a/2+2) 1 1 1 z` |
| `(10)^(a/2+2) 1 …` | a/2 + 2 Kd2 steps (`Kd2_loop`) | `1 1 1 z` |
| `1 1 1 z` | one Kd1 step (`Kd1_step_all`) | `1 z` |

    Ce_gen p a 0 (1 0 0 1 z)  →+  Ce_gen (Round_map (p, a)) 0 (1 z)                         [Full_Round]
    Round_map (p, a) = Kd1_step (Kd2_iter (a/2 + 2) (Kd2_alt_iter (p − 2) pa_0))

A round is p − 2 f_(ω+2) steps from the fixed start pa_0, then a/2 + 2 more and one Kd1 step: about f_(ω+3) of the
old level. The
header `1 0 0 1` becomes `1`, so each round uses up one header in the tail.

### The halt

From `Ce_gen p a 0 (1)` (a lone 1 followed by blanks), E writes 1 at h, F crosses the 1 at h + 1, I0 writes 0 at
h + 2, N0 writes 1 at h + 3 and moves right, and Q reads the 0 at h + 4: Q0 is the halt, after four steps
(`HALT_step`).

## 2. The run

| phase | what runs | result |
|---|---|---|
| opening | as in M16_B: `init_ce0` (21854 steps, to `Ce_gen 0 4 0 (1^230)`), then `start_boot` | pa_0: `Ce_gen 26 W_21(1) 0 ((10)^10 0 1 0 0 1^228)` [`init_ce`] |
| round 1 | 9 Kd2 steps on (10)^9, as in M16_B | pa_R1 = `Kd2_iter 9 pa_0`, tail `1 0 0 1 0 0 1^228` [`Kd2_loop`] |
| round 2 | `Full_Round` with z = `0 0 1^228` | pa_R2 = `Round_map pa_R1`, tail `1 0 0 1^228` |
| round 3 | `Full_Round` with z = `1^227` | pa_R3 = `Round_map pa_R2`, tail `1^228` |
| level 2 | 114 Kd1 steps | pa_R3_114 = `Kd1_iter 114 pa_R3`, tail blank [`Kd1_loop`] |
| last cycle | one D1 cycle on the blank: `0 → 1` | pa_final = `D1_cycle pa_R3_114`, tail `1` [`D1_cycle_all`] |
| halt | E, F, I, N, then Q reads 0 | `c_end` pa_final [`HALT_step`, `run_to_end`, `halt`] |

Round 1 is M16_B's level-3 loop. In M16_B, the tail `1 0 0 1 0 0 1^228` that follows it is the bridge; here it is
two round headers. The halting tape is 0^∞ (10)^p 1^(a+2) 1 1 0 1 [Q on 0] 0^∞ with (p, a) = pa_final, which holds
p + a + 5 ones (`ones_c_end`, `score_exact`).

**Size** (`BB17_halt_fw3.v`, sections "Fast-Growing Hierarchy …" and "Domination …"). `ok_pa n (p, a)` says n ≤ p − 5 and 4n + 6 ≤ a. The start
satisfies ok_pa 9 pa_0 (`ok_pa_0`). Round 1 gives ok_pa f_(ω+3)(9) (`Kd2_iter_dom`: 9 steps of f_(ω+2)). A round maps
ok_pa n to ok_pa f_(ω+3)(n) (`Round_map_dom`): the alt loop from pa_0 is f_(ω+2)^(p−2)(9) ≥ n, and then
a/2 + 2 ≥ n Kd2 steps follow. That gives f_(ω+3)^2(9) after round 2. In round 3, n ≥ 110 (`f_omega3_9_ge_110`), so
a/2 + 2 ≥ n + 115, and the round gives f_(ω+2)^115(f_(ω+3)(n)) (`Round_map_dom_115`). The 114 Kd1 steps keep the
bound (`Kd1_iter_dom`), and the last D1 cycle adds one more f_(ω+2) (`D1_cycle_dom`). So
f_(ω+2)^116(f_(ω+3)^3(9)) ≤ p − 5 at the halt (`halt_f_omega3`), and f_(ω+2)^116(f_(ω+3)^3(9)) < N
(`sigma_lower_bound`). The exponent 116 is 115 Kd2 steps of round 3 beyond the f_(ω+3) count, plus the final D1
cycle; it is not 116 separate cycles after the rounds.

## 3. Verification

[`verify/`](verify/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 40 s, built in CI (job
`bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above (34 checks
generated from the string) and the blank start configuration. It prints the definitions the statements use and
confirms that `halt`, `score_exact`, `sigma_lower_bound` and `sigma_lower_bound_fw3_3` are closed under the global
context.

[`tools/bb17_writeup_chk.py`](tools/bb17_writeup_chk.py) simulates the machine string cell by cell, without the Coq
files (about 10 s). It checks:

- the opening reaches `Ce_gen 0 4 0 (1^230)` after 21854 steps, and in its first 10^7 steps reads none of N0, O1,
  P0, Q0, Q1 (so up to there the run is M16_B's); it reads N1, O0 and P1;
- `SWEEP_M17B` on 49 instances (p = 1..7, a = 0..12 even, random z): the claimed configuration after 4p + a + 14
  steps, z never read;
- `bounce_156` and the first part of `P0_bounce` (to `Ce_gen 22 8 1 (0 r)`, step 1627) on five tails r, and
  `CE_EVEN` on 45 small instances;
- the halt from `Ce_gen p a 0 (1)` on 16 instances: four steps, then Q reads 0, with p + a + 5 ones;
- the engine pieces `D1_REL`, `C_REL_full` and `D2_STEP_full` on small instances: they reach the stated
  configurations, and only `C_REL_full` and `D2_STEP_full` read slots outside A–M (N1, O0, P1).

The rest of the run is too large to simulate: a_0 = W_21(1) is already astronomically large.

## 4. Comparisons (an argument, not a Coq lemma)

The comparisons below are arguments on paper. No Coq lemma compares this machine with another entry: none of the
machines below has a proved upper bound.

- f_(ω+3)(9) = f_(ω+2)^9(9) > 115.
- **BB18_fw3** ([`../BB18/`](../BB18/), the previous BB(18) entry): proved f_(ω+2)(f_(ω+3)(114)) < N. Since
  f_(ω+3)(9) > 115, f_(ω+3)^2(9) > f_(ω+3)(115) = f_(ω+2)^115(115) > f_(ω+2)(f_(ω+2)^114(114)) =
  f_(ω+2)(f_(ω+3)(114)). So already two of M17_B's three rounds are above BB18_fw3's proved lower bound, with one
  fewer state.
- **M16_B** ([`../BB16/`](../BB16/), BB(16) entry): proved f_(ω+2)(f_(ω+3)(9)) = f_(ω+2)^10(9) < N, which is below
  f_(ω+3)(10) < f_(ω+3)^2(9). As of 2026-11-03 the wiki's BB(17) row is empty, so through BB(17) ≥ BB(16), M16_B's
  bound was the published lower bound for BB(17).
- **The earlier f_(ω+2)-class BB(17) champion** (Jacobzheng, wiki bound f_(ω+2)(f_(ω+1)^2(f_ω^2(60)))): its analysis
  gives an f_(ω+2)-class score, far below f_(ω+3)(9).
- **M18_4round** ([`../BB18/`](../BB18/), the BB(18) entry) and **M19_fw4** ([`../BB19/`](../BB19/), BB(19)) are
  above M17_B's bound, and the wiki's BB(20) champion (Jacobzheng, f_(ω+7)(f_(ω+7)(5))) is far above all of them.
- Not yet reviewed by the bbchallenge community.

## 5. Relation to other entries

- **M16_B** (BB(16)): same rows A–M and the same slots N1, O0, P1, so the same opening and the same round 1. M16_B
  writes a finite program and halts when it runs out. M17_B changes N0, O1, P0 and adds Q, so that the tail
  `1 0 0 1 …` after round 1 is read as two round headers instead of M16_B's bridge.
- **BB18_fw3** (Argon's BB16_fw4 engine and a two-state counter): it also restarts the level at each pass, but by
  reflecting the whole stack with P_BOOT and a P walk. M17_B's bounce restarts at the fixed level pa_0 and runs
  `Kd2_alt_loop` over the old level, then `Kd2_loop` over the old accumulator.
- **M18_4round** ([`../BB18/`](../BB18/), the BB(18) entry): the same rows A–P and the same bounce. Q is changed
  (Q0 = `1RR`, Q1 = `0LO`) and a new state R reads the tail headers, which gives four rounds.
- Argon's report on this search also lists siblings that are not entries and were not checked in Coq here: M17_A
  (Q1 = `0LO`, two rounds, so below M17_B) and two 15-state machines, M15_A and M15_B, that halt right after
  M16_B's round 1. Their stated bound 2·f_(ω+3)(9) = 2·f_(ω+2)^9(9) is below M14b's proved
  f_(ω+2)^9(f_(ω+1)(f_(ω+1)(3))) ([`../BB14/`](../BB14/)), because f_(ω+1)(f_(ω+1)(3)) > 10, so they do not improve
  on BB(15) ≥ BB(14).

## Credit

Found and proved in Coq by Argon (a Google Gemini model run by the repository owner in Google's Antigravity),
2026-11-02: the machine and `BB17_halt_fw3.v` with `halt`, `score_exact`, `sigma_lower_bound` and
`sigma_lower_bound_fw3_3`. This project (the repository owner with Claude models (Anthropic) as agents) wrote the
write-up, the probe and the literal checker, did the packaging, and re-checked the proofs (from-scratch build,
`Print Assumptions`, the probe).
