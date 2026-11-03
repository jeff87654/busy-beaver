# M18_4round: an 18-state machine at level f_(ω+3), four rounds

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1LN_0RB1LI_1RR0LO_0RO1RZ

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
| Q | 1RR | 0LO | new (M17_B: `1RZ 1LO`)                                           |
| R | 0RO | 1RZ | new: R1 is the halt                                              |

Rows A–P are those of M17_B ([`../BB17/`](../BB17/)); rows A–M and the slots N1, O0 and P1 are those of M16_B
([`../BB16/`](../BB16/)). Both are Argon's.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB18_4round_fw3.halt`. |
| Exact score | Machine-checked formula: N = p + a + 233 ones at the halt, where (p, a) = `pa_R4` is given by the recursion of section 2 (`score_exact`). The halt R1 = `1RZ` is read on a 1 and writes 1, so σ = N = p + a + 233. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+3)^4(9) < N = σ (`sigma_lower_bound`). |
| Comparisons | **Argument, not a Coq lemma** (section 4): above M17_B's proved f_(ω+2)^116(f_(ω+3)^3(9)), and so above BB18_fw3's (the previous BB(18) entry). Not yet reviewed by the bbchallenge community. |
| Steps | Not computed. |

## 1. How it works

### The core and the bounce (shared with M17_B)

Read the M17_B write-up ([`../BB17/`](../BB17/)) first. The configuration family is

    Ce_gen p a c r  =  0^∞ (10)^p 1^(a+2) [E] (10)^c 0 r        (head on the cell after the 1s, state E)

and the engine reads the tail X of `Ce_gen p a 0 X` as a program. In this file the rules are stated as follows:

- `1 1 r` → `r`: one Kd1 step, f_(ω+1) (`Kd1_step_all`);
- `0 r` → `1 r`: one D1 cycle, f_(ω+2) (`D1_cycle_all`);
- `1 0 1 0 r` → `1 0 r`: one Kd2 step, f_(ω+2) (`Kd2_step_all`); so `(10)^m 1 0 r` → `1 0 r` (`Kd2_loop`);
- `0 1 0 r` → `0 r`: one `Kd2_alt_step` (a D1 cycle, then a Kd1 step), f_(ω+2) (`Kd2_alt_step_all`); so
  `0 (10)^m r` → `0 r` (`Kd2_alt_loop`).

None of these reads N0, O1, P0, Q or R; every Kd1 and Kd2 step reads N1, O0 and P1 in a short turnaround, as in
M16_B. The bounce is M17_B's (P0 = `0RB`; here the lemma is called `bounce_155`, M17_B's file calls it
`bounce_156`; both are 156 steps):

    P on the left-end 0, then (10)^3 r  →+  Ce_gen 26 W_21(1) 0 (0 r)                            [P0_bounce]

It eats three (10) tokens and restarts the engine at the level pa_0 = (26, W_21(1)) that the opening reaches.

### The new slots: two sweeps

Q and R are new or changed, and they make two kinds of round header. With h the head cell of `Ce_gen p a 0 …`:

- Header `1 0 0 1`: E, F, I and N0 run as in M17_B, and Q reads the 1 at h + 4. Q1 = `0LO` clears it (M17_B's Q1
  kept it). O and N then walk left as in M17_B, and P reaches the left end. After 4p + a + 14 steps:

      Ce_gen p a 0 (1 0 0 1 u)  →+  P on the left-end 0, then (10)^(p+1) 0 (10)^(a/2+2) 0 u            [SWEEP_1]

- Header `1 0 0 0 0 1`: Q reads 0 at h + 4, writes 1 and moves right (Q0 = `1RR`). R reads 0 at h + 5, leaves it
  and moves right (R0 = `0RO`), and O meets the 1 at h + 6. From there the sweep runs as before. After
  4p + a + 20 steps:

      Ce_gen p a 0 (1 0 0 0 0 1 u)  →+  P on the left-end 0, then (10)^(p+1) 0 (10)^(a/2+2) 0 1 0 u    [SWEEP_001]

- Header `1 0 0 0 1`: Q0 writes 1 at h + 4 and moves right, and R reads the 1 at h + 5: R1 is the halt, after five
  steps (`HALT_step`).

### One round

After either sweep, the round runs the same way (`ROUND_after_sweep`, for p ≥ 5 and a ≥ 4 even):

| from tail | what runs | to tail |
|---|---|---|
| P at the left end: `(10)^(p+1) 0 (10)^(a/2+2) 0 u` | bounce | `0 (10)^(p−2) 0 (10)^(a/2+2) 0 u` at level pa_0 |
| `0 (10)^(p−2) …` | p − 2 alt steps (`Kd2_alt_loop`) | `0 0 (10)^(a/2+2) 0 u` |
| `0 …` | one D1 cycle (`D1_cycle_all`) | `1 0 (10)^(a/2+2) 0 u` = `(10)^(a/2+2) 1 0 0 u` |
| `(10)^(a/2+2) 1 0 …` | a/2 + 2 Kd2 steps (`Kd2_loop`) | `1 0 0 u` |

    Round_step (p, a) = Kd2_iter (a/2 + 2) (D1_cycle (Kd2_alt_iter (p − 2) pa_0))
    Ce_gen p a 0 (1 0 0 1 u)        →+  Ce_gen (Round_step (p, a)) 0 (1 0 0 u)                 [Round_1_step]
    Ce_gen p a 0 (1 0 0 0 0 1 u)    →+  Ce_gen (Round_step (p, a)) 0 (1 0 0 1 0 u)             [Round_001_step]

So a round is p − 2 f_(ω+2) steps from the fixed start pa_0, one D1 cycle, and a/2 + 2 more f_(ω+2) steps: about
f_(ω+3) of the old level. Unlike M17_B's round, it ends without a Kd1 step and leaves `1 0 0` in front of the rest of
the tail, so the next header is read from what follows.

## 2. The run

| phase | what runs | result |
|---|---|---|
| opening | as in M16_B: `init_ce0` (21854 steps, to `Ce_gen 0 4 0 (1^230)`), then `start_boot` | pa_0: `Ce_gen 26 W_21(1) 0 ((10)^10 0 1 0 0 1^228)` [`init_ce`] |
| round 1 | 9 Kd2 steps on (10)^9, as in M16_B | pa_R1 = `Kd2_iter 9 pa_0`, tail `1 0 0 1 0 0 1^228` [`Kd2_loop`] |
| round 2 | `Round_1_step` with u = `0 0 1^228` | pa_R2 = `Round_step pa_R1`, tail `1 0 0 0 0 1^228` |
| round 3 | `Round_001_step` with u = `1^227` | pa_R3 = `Round_step pa_R2`, tail `1 0 0 1 0 1^227` |
| round 4 | `Round_1_step` with u = `0 1^227` | pa_R4 = `Round_step pa_R3`, tail `1 0 0 0 1^227` |
| halt | E, F, I, N, Q, then R reads 1 | `c_end` pa_R4 [`HALT_step`, `run_to_end`, `halt`] |

The tail `1 0 0 1 0 0 1^228` after round 1 is the same as in M17_B, but here it holds three headers: each round
leaves `1 0 0`, and the next sweep reads it together with the cells after it. The 227 ones at the end are never
consumed. The halting tape is 0^∞ (10)^p 1^(a+2) 1 1 0 1 1 [R on 1] 1^226 0^∞ with (p, a) = pa_R4, which holds
p + a + 233 ones (`ones_c_end`, `score_exact`). The halting transition writes 1 on that 1, so σ = N.

**Size** (`BB18_4round_fw3.v`, sections "Fast-Growing Hierarchy …" and "Domination …"). `ok_pa n (p, a)` says
n ≤ p − 5 and 4n + 6 ≤ a. The start satisfies ok_pa 9 pa_0 (`ok_pa_0`). Round 1 gives ok_pa f_(ω+3)(9)
(`Kd2_iter_dom`). Each later round maps ok_pa n to ok_pa f_(ω+3)(n) (`Round_step_dom`): the alt loop from pa_0 is
f_(ω+2)^(p−2)(9) ≥ n, the D1 cycle raises it, and then a/2 + 2 ≥ n Kd2 steps follow. After three more rounds,
f_(ω+3)^4(9) ≤ p − 5 (`halt_f_omega3_4`), so f_(ω+3)^4(9) < N (`sigma_lower_bound`). Like M17_B's round 3, every
round has slack (a/2 + 2 is far more than n), but the file proves only this bound.

## 3. Verification

[`verify_m18r4/`](verify_m18r4/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 50 s, built in CI
(job `bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above (36 checks
generated from the string) and the blank start configuration. It prints the definitions the statements use and
confirms that `halt`, `score_exact` and `sigma_lower_bound` are closed under the global context.

[`tools/bb18_4round_writeup_chk.py`](tools/bb18_4round_writeup_chk.py) simulates the machine string cell by cell,
without the Coq files (about 10 s). It checks:

- the opening reaches `Ce_gen 0 4 0 (1^230)` after 21854 steps, and in its first 10^7 steps reads none of N0, O1,
  P0, Q0, Q1, R0, R1 (so up to there the run is M16_B's); it reads N1, O0 and P1;
- `SWEEP_1` and `SWEEP_001` on 49 instances each (p = 1..7, a = 0..12 even, random u): the claimed configurations
  after 4p + a + 14 and 4p + a + 20 steps, u never read;
- `bounce_155` and the first part of `P0_bounce` (to `Ce_gen 22 8 1 (0 r)`, step 1627) on five tails r, and
  `CE_EVEN` on 45 small instances;
- the halt from `Ce_gen p a 0 (1 0 0 0 1^227)` on 16 instances: five steps, then R reads 1, with p + a + 233 ones;
- the engine pieces `D1_REL`, `C_REL_full` and `D2_STEP_full` on small instances: they reach the stated
  configurations, and only `C_REL_full` and `D2_STEP_full` read slots outside A–M (N1, O0, P1).

The rest of the run is too large to simulate: a_0 = W_21(1) is already astronomically large.

## 4. Comparisons (an argument, not a Coq lemma)

The comparisons below are arguments on paper. No Coq lemma compares this machine with another entry: none of the
machines below has a proved upper bound.

- **M17_B** ([`../BB17/`](../BB17/), BB(17) entry): proved f_(ω+2)^116(X) < N with X = f_(ω+3)^3(9). Here
  f_(ω+3)^4(9) = f_(ω+3)(X) = f_(ω+2)^X(X), and X > 116, so f_(ω+3)^4(9) > f_(ω+2)^116(X).
- **BB18_fw3** (the previous BB(18) entry, below): proved f_(ω+2)(f_(ω+3)(114)) < N, which is below
  f_(ω+3)^2(9) (M17_B write-up, section 4), and so far below f_(ω+3)^4(9).
- **The earlier f_(ω+2)-class BB(18) champion** (Jacobzheng, wiki bound f_(ω+2)(f_(ω+1)^3(f_ω^2(60)))): its analysis
  gives an f_(ω+2)-class score, far below f_(ω+3)(9).
- **M19_fw4** ([`../BB19/`](../BB19/), BB(19) entry): proved f_(ω+4)(f_(ω+2)(114)) < N, above f_(ω+3)^4(9). The
  wiki's BB(20) champion (Jacobzheng, f_(ω+7)(f_(ω+7)(5))) is far above all of them.
- Not yet reviewed by the bbchallenge community.

## 5. Relation to other entries

- **M17_B** (BB(17)): the same rows A–P. M17_B's round turns the header `1 0 0 1` into `1`, so the tail written
  by the opening holds two headers, and M17_B ends with 114 Kd1 steps on the 1^228 and one more D1 cycle. Here Q1
  clears the header's last 1, the round leaves `1 0 0`, and R reads one more cell, so the same tail holds three
  headers and the 1^227 is not consumed.
- **M16_B** (BB(16)): the same rows A–M; the opening and round 1 are M16_B's.
- **BB18_fw3** (previous BB(18) entry, below): Argon's BB16_fw4 engine with a two-state counter on N0; one full
  reflection pass of p − 4 Kd2 steps, so f_(ω+2)(f_(ω+3)(114)).
- Argon's report on this search lists two siblings with R0 = `1RN` and R0 = `1RQ`, and an 18-state three-round
  family (M18_R); they were not checked here.

## Credit

Found and proved in Coq by Argon (a Google Gemini model run by the repository owner in Google's Antigravity),
2026-11-02: the machine and `BB18_4round_fw3.v` with `halt`, `score_exact` and `sigma_lower_bound`. This project
(the repository owner with Claude models (Anthropic) as agents) wrote the write-up, the probe and the literal
checker, did the packaging, and re-checked the proofs (from-scratch build, `Print Assumptions`, the probe).
