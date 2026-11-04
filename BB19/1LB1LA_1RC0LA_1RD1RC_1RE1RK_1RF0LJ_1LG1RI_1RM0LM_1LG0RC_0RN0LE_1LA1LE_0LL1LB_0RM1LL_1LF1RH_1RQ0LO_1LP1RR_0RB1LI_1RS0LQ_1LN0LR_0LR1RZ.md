# M19_fw4_A: a 19-state machine at level f_(ω+4), on the M17_B core

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1RR_0RB1LI_1RS0LQ_1LN0LR_0LR1RZ

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
| N | 1RQ | 0LO | N0 starts the sweep (as in M17_B and M18_4round)                 |
| O | 1LP | 1RR | O1 changed (M17_B, M18_4round: `1LN`)                            |
| P | 0RB | 1LI | P0 is the left-end bounce (as in M17_B and M18_4round)           |
| Q | 1RS | 0LQ | changed (M18_4round: `1RR 0LO`)                                  |
| R | 1LN | 0LR | changed (M18_4round: `0RO 1RZ`)                                  |
| S | 0LR | 1RZ | new: S1 is the halt                                              |

Rows A–N and P are those of M17_B ([`../BB17/`](../BB17/)) and M18_4round ([`../BB18/`](../BB18/)); O differs only in
O1. All three machines are Argon's. This machine is **not** built on BB18_fw3's or M19_fw4's engine (BB16_fw4, with
I0 = `1RN`); it uses the M17_B core with the left-end bounce.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB19_fw4_fw3_9.halt`. |
| Exact score | Machine-checked formula: N = p + a + 234 ones at the halt, where (p, a) = `pa_final` is given by the recursion of section 2 (`score_exact`). The halt S1 = `1RZ` is read on a 1 and writes 1, so σ = N = p + a + 234. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+4)(f_(ω+3)(9)) < N = σ (`sigma_lower_bound`; the file also states it as `sigma_bound`). |
| Comparisons | **Argument, not a Coq lemma** (section 4): above the proved bound of M19_fw4 (f_(ω+4)(f_(ω+2)(114))) and the BB(18) entries here. **Not a BB(19) record**: the bbchallenge wiki's BB(19) champion (Jacobzheng, > f_(ω+7)^2(5), checked 2026-11-04) is far larger. Not yet reviewed by the bbchallenge community. |
| Steps | Not computed. |

## 1. How it works

### The core and the bounce (shared with M17_B and M18_4round)

Read the M18_4round write-up ([`../BB18/`](../BB18/), section 1) first. The configuration family is

    Ce_gen p a c r  =  0^∞ (10)^p 1^(a+2) [E] (10)^c 0 r        (head on the cell after the 1s, state E)

and the engine reads the tail X of `Ce_gen p a 0 X` as a program. The rules used here, all parametric in the rest
of the tail r (so r is never read or moved):

- `1 1 r` → `r`: one Kd1 step, f_(ω+1) (`Kd1_step_all`); so `1^(2m) r` → `r` (`Kd1_loop`);
- `0 r` → `1 r`: one D1 cycle, f_(ω+2) (`D1_cycle_all`);
- `1 0 1 0 r` → `1 0 r`: one Kd2 step, f_(ω+2) (`Kd2_step_all`); so `(10)^m 1 0 r` → `1 0 r` (`Kd2_loop`);
- `0 1 0 r` → `0 r`: one `Kd2_alt_step` (a D1 cycle, then a Kd1 step), f_(ω+2) (`Kd2_alt_step_all`); so
  `0 (10)^m r` → `0 r` (`Kd2_alt_loop`).

None of these reads N0, O1, P0 or the states Q, R, S; the Kd1 and Kd2 steps read N1, O0 and P1 in a short
turnaround, as in M16_B. The bounce is M17_B's (P0 = `0RB`, 156 steps for `bounce_155`):

    P on the left-end 0, then (10)^3 r  →+  Ce_gen 26 W_21(1) 0 (0 r)                            [P0_bounce]

It eats three (10) tokens and restarts the engine at the fixed level pa_0 = (26, W_21(1)) that the opening reaches.

### The new slots: two sweeps and the halt

A round starts when the engine reaches a tail that begins with `1 0 0`. Write h for the head cell of
`Ce_gen p a 0 X`, so X starts at h + 1. In all three cases E, F, I and N run as in M17_B: E writes 1 at h, F passes
the 1 at h + 1, I leaves the 0 at h + 2, and N0 = `1RQ` writes 1 at h + 3 and hands over to Q at h + 4.

- **Header `1 0 0 1`: the parking sweep.** Q reads the 1 at h + 4. Q1 = `0LQ` erases it and the 1 that N wrote at
  h + 3; Q0 = `1RS` writes 1 at h + 2, and S0 = `0LR` turns back. Now R1 = `0LR` walks left and erases every 1 it
  meets: h + 2, h + 1, h and the whole accumulator block 1^(a+2). At the 0 of the last (10) pair of the stack,
  R0 = `1LN` hands over to the N/O/P walk of M17_B, which carries P to the left end. After 4p + a + 12 steps:

      Ce_gen p a 0 (1 0 0 1 u)  →+  P on the left-end 0, then (10)^(p+1) 0^(a+6) u                 [SWEEP_park]

  The accumulator is gone; in its place there are a + 6 blank cells.

- **Header `1 0 0 0 0`: the countdown sweep.** Q reads 0 at h + 4: Q0 = `1RS` writes 1 and moves right, and S reads
  0 at h + 5 (S0 = `0LR`, back left). R1 erases the 1s at h + 4 and h + 3, and R0 = `1LN` writes 1 at h + 2. Then
  the loop N1 = `0LO`, O1 = `1RR`, R0 = `1LN` walks left over the block of ones, three steps per cell, and leaves it
  as ones. At the stack, O0 = `1LP` starts the N/O/P walk. After 4p + 3a + 20 steps:

      Ce_gen p a 0 (1 0 0 0 0 u)  →+  P on the left-end 0, then (10)^(p+1) 1^(a+4) 0 0 0 u          [SWEEP_cd]

  Here the accumulator survives as a block of a + 4 ones, and the header has moved one cell to the right.

- **Header `1 0 0 0 1`: the halt.** Q0 writes 1 at h + 4 and moves right, and S reads the 1 at h + 5: S1 is the
  halt, after five steps (`HALT_step`).

### The rounds

After either sweep, P0 bounces (`P0_bounce`), and the p − 2 remaining (10) tokens are eaten by `Kd2_alt_loop`
from the fixed start level pa_0. What follows depends on the sweep:

| round | from tail after the bounce | what runs | to tail |
|---|---|---|---|
| parking | `0 (10)^(p−2) 0^(a+6) u` | p − 2 alt steps, one D1 cycle | `1 0 0 0^(a+4) u` |
| countdown | `0 (10)^(p−2) 1^(a+4) 0 0 0 u` | p − 2 alt steps, one D1 cycle, a/2 + 2 Kd1 steps | `1 0 0 0 u` |

    Kpark   (p, a) = D1_cycle (Kd2_alt_iter (p − 2) pa_0)
    Kcd_step (p, a) = Kd1_iter (a/2 + 2) (Kpark (p, a))
    Ce_gen p a 0 (1 0 0 1 r)        →+  Ce_gen (Kpark (p, a)) 0 (1 0 0 0^(a+4) r)                 [Kpark_all]
    Ce_gen p a 0 (1 0 0 0 0 u)      →+  Ce_gen (Kcd_step (p, a)) 0 (1 0 0 0 u)                    [Kcd_step_all]

Each round is about p f_(ω+2) steps from the fixed start pa_0, so f_(ω+3) of the old level
(`iter_f_omega2_ge_f_omega3`). The parking round does not use a for growth: it turns a into a + 6 blank cells. In
a countdown round the D1 cycle makes the tail `1 1^(a+4) 0 0 0 u`, and a/2 + 2 Kd1 steps eat the ones again.

**The counter.** The tail right of the boundary is the header `1 0 0 0`, then a run of m zeros, then a fixed wall
u. Each countdown round turns `1 0 0 0 0^(m+1) u` into `1 0 0 0 0^m u` (`Kcd_loop`): the header moves one cell right,
towards the wall, and the wall is never touched. When m = 0 the header is `1 0 0 0 1`, and the machine halts.

## 2. The run

| phase | what runs | result |
|---|---|---|
| opening | as in M16_B, M17_B and M18_4round: `init_ce0` (21854 steps, to `Ce_gen 0 4 0 (1^230)`), then `start_boot` | pa_0: `Ce_gen 26 W_21(1) 0 ((10)^10 0 1 0 0 1^228)` [`init_ce`] |
| round 1 | 9 Kd2 steps on (10)^9, as in M16_B | pa_R1 = `Kd2_iter 9 pa_0`, tail `1 0 0 1 0 0 1^228` [`Kd2_loop`] |
| round 2 (parking) | `Kpark_all` with r = `0 0 1^228` | `Kpark pa_R1`, tail `1 0 0 0 0^(a_R1+5) 1^228`, where a_R1 = snd pa_R1 |
| rounds 3 to a_R1 + 7 (countdown) | `Kcd_loop`: a_R1 + 5 countdown rounds | pa_final = `Kcd_iter (a_R1 + 5) (Kpark pa_R1)`, tail `1 0 0 0 1^228` |
| halt | E, F, I, N, Q, then S reads 1 | `c_end` pa_final [`HALT_step`, `run_to_end`, `halt`] |

The tail written by the opening is the same as in M17_B and M18_4round. Round 1 leaves the header `1 0 0 1`, and the
1^228 at the end becomes the wall. The halting tape is 0^∞ (10)^p 1^(a+2) 1 1 0 1 1 [S on 1] 1^227 0^∞ with
(p, a) = pa_final; S reads the first 1 of the wall. It holds p + a + 234 ones (`ones_c_end`, `score_exact`). The
halting transition writes 1 on that 1, so σ = N.

**Size** (`BB19_fw4_fw3_9.v`, sections "Fast-Growing Hierarchy …" and "Domination …"). `ok_pa n (p, a)` says
n ≤ p − 5 and 4n + 6 ≤ a.

- The start satisfies ok_pa 9 pa_0 (`ok_pa_0`), and round 1 gives ok_pa (2 · f_(ω+3)(9)) pa_R1 (`pa_R1_dom`), so
  a_R1 ≥ 8 · f_(ω+3)(9) + 6.
- `Kpark_dom` and `Kcd_step_dom`: if ok_pa (2n) holds at the start of a round, ok_pa (2 · f_(ω+3)(n)) holds after it.
  The alt loop runs p − 2 ≥ 2n steps from pa_0, which gives f_(ω+2)^(p−2)(9) ≥ f_(ω+3)(n), and the D1 cycle raises it.
- `Kcd_iter_dom`, `pa_final_dom`: after the parking round and a_R1 + 5 countdown rounds,
  ok_pa (2 · f_(ω+3)^(a_R1+6)(f_(ω+3)(9))) pa_final. Since a_R1 + 6 ≥ f_(ω+3)(9), that is at least
  f_(ω+3)^(f_(ω+3)(9))(f_(ω+3)(9)) = f_(ω+4)(f_(ω+3)(9)), so f_(ω+4)(f_(ω+3)(9)) < a < N (`sigma_lower_bound`).

The bound uses only f_(ω+3)(9) of the a_R1 + 6 rounds after round 1. A sharper bound is not needed.

## 3. Verification

[`verify_m19a/`](verify_m19a/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 50 s, built in CI
(job `bb13-bb14`). Argon's proof file is published unchanged. `probe.v` re-checks the transition table entry by
entry against the string above (38 checks generated from the string) and the blank start configuration. It prints
the definitions the statements use and confirms that `halt`, `score_exact` and `sigma_lower_bound` are closed under
the global context.

[`tools/m19a_writeup_chk.py`](tools/m19a_writeup_chk.py) simulates the machine string cell by cell, without the Coq
files (about 10 s). It checks:

1. the opening reaches `Ce_gen 0 4 0 (1^230)` after 21854 steps, and in its first 10^7 steps reads no slot of N, O,
   P, Q, R, S other than N1, O0 and P1 (so up to there the run is M16_B's);
2. `SWEEP_park` and `SWEEP_cd` on 49 instances each (p = 1..7, a = 0..12 even, random u): the claimed configurations
   after 4p + a + 12 and 4p + 3a + 20 steps, u never read;
3. `bounce_155` and the first part of `P0_bounce` (to `Ce_gen 22 8 1 (0 r)`, step 1627) on five tails r, and
   `CE_EVEN` on 45 small instances;
4. the halt from `Ce_gen p a 0 (1 0 0 0 1^228)` on 16 instances: five steps, then S reads 1, with p + a + 234 ones;
5. the engine pieces `D1_REL`, `C_REL_full` and `D2_STEP_full` on small instances: they reach the stated
   configurations, and read no slot of N–S other than N1, O0 and P1;
6. the right end of the whole run from the end of round 1, for a_R1 = 4, 6, 8, 10, 20, 40: the sweeps and the halt
   run literally, and the rest of each round (bounce, alt loop, D1 cycle, Kd1 steps) is replaced by its tape effect
   from the lemmas above, with a fresh small level at each round. The parking round leaves a_R1 + 5 zeros before the
   wall, exactly a_R1 + 5 countdown rounds follow, each moves the boundary one cell right, and S halts on the first
   cell of the wall, which never moves.

The rest of the run is too large to simulate: a_0 = W_21(1) is already astronomically large.

## 4. Comparisons (an argument, not a Coq lemma)

The comparisons below are arguments on paper. No Coq lemma compares this machine with another entry: none of them
has a proved upper bound.

- f_(ω+4)(n) = f_(ω+3)^n(n), by the definition, and f_(ω+3), f_(ω+4) are increasing with x ≤ f(x).
- **M19_fw4** (the previous entry here): proved f_(ω+4)(f_(ω+2)(114)) < N. Since
  f_(ω+3)(9) = f_(ω+2)^9(9) ≥ f_(ω+2)(f_(ω+2)(9)) > f_(ω+2)(114), the bound here is larger.
- **BB(18) entries** ([`../BB18/`](../BB18/)): M18_229round, proved f_(ω+3)^229(9), and M18_4round, proved
  f_(ω+3)^4(9). With n = f_(ω+3)(9) > 229: f_(ω+3)^n(n) ≥ f_(ω+3)^229(9). So the bound here is above both.
- **BB(19): not a record.** The bbchallenge wiki's Champions page (checked 2026-11-04) lists a BB(19) champion by
  Jacobzheng with the lower bound f_(ω+7)^2(5), for `1RQ1RL_0LI1RC_0LD1LF_0RA1LD_1RB1RE_1LH0LG_1LF1LG_1RE1RM_1LJ1LI_0LK1LI_1RL1RA_0RL0RE_0LN1RM_1LO0LO_1RE1LP_1LN1LN_1LR1RQ_1RZ1LS_0LE0LR`
  (marked "Not independently verified"). That is far above anything at level f_(ω+4). The wiki's BB(20) champion
  (Jacobzheng, > f_(ω·2)(f_(ω+2)^2(f_10(2)))) is larger still.
- Not yet reviewed by the bbchallenge community.

## 5. Relation to other entries

- **M18_4round** (BB(18), [`../BB18/`](../BB18/)): the same rows A–N and P, the same opening, round 1 and bounce.
  Its sweeps turn the accumulator into (10) tokens that Kd2 steps eat, so each round is one f_(ω+3) step and the
  tail written by the opening holds three round headers: four rounds in all. Here the parking sweep erases the
  accumulator instead, and the blank cells it leaves are a counter of a_R1 + 5 more rounds.
- **M17_B** (BB(17), [`../BB17/`](../BB17/)): the same rows A–N and P, and O0; the core and the bounce come from
  there.
- **M19_fw4** (the previous entry here): a different engine (Argon's BB16_fw4, as in BB18_fw3) with another parking
  trick: it parks the accumulator as a block of ones to the right and erases two of them per pass.

## Credit

Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity (2026-11-03):
the machine and `BB19_fw4_fw3_9.v` with `halt`, `score_exact`, `sigma_bound` and `sigma_lower_bound`; re-checked
here. This project (the repository owner with Claude models (Anthropic) as agents) wrote the write-up, the probe and
the literal checker, did the packaging, and re-checked the proofs (from-scratch build, `Print Assumptions`, the
probe).
