# M16_B: a 16-state machine at level f_(ω+3)

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RO0LO_1LP1RM_1RZ1LI

|   | 0   | 1   |                                                        |
|---|-----|-----|--------------------------------------------------------|
| A | 1LB | 1LA |                                                        |
| B | 1RC | 0LA |                                                        |
| C | 1RD | 1RC |                                                        |
| D | 1RE | 1RK |                                                        |
| E | 1RF | 0LJ |                                                        |
| F | 1LG | 1RI |                                                        |
| G | 1RM | 0LM |                                                        |
| H | 1LG | 0RC |                                                        |
| I | 0RN | 0LE | I0 writes 0 (BB16_fw4: `1RN`)                          |
| J | 1LA | 1LE |                                                        |
| K | 0LL | 1LB |                                                        |
| L | 0RM | 1LL |                                                        |
| M | 1LF | 1RH |                                                        |
| N | 0RO | 0LO | new row (BB16_fw4: `0LP 0RG`)                          |
| O | 1LP | 1RM | new row (BB16_fw4: `0LG 1LP`)                          |
| P | 1RZ | 1LI | new row (BB16_fw4: `0LO 1LP`); P0 is the halt          |

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB16_halt_fw3.halt`. |
| Exact score | Machine-checked formula: N = p + a + 5 ones at the halt, where (p, a) = `pa_11` is given by the recursion of section 2 (`score_exact`). The halt P0 = `1RZ` is read on a 0, so σ = N + 1 = p + a + 6. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+2)(f_(ω+3)(9)) < N (`sigma_lower_bound`; Argon's `halt_f_omega3` states f_(ω+2)(f_(ω+3)(9)) ≤ p − 5). |
| Comparisons | **Argument, not a Coq lemma** (section 4): f_(ω+2)(f_(ω+3)(9)) = f_(ω+2)^10(9) is above M14b's proved f_(ω+2)^9(f_(ω+1)(f_(ω+1)(3))) and the f_(ω+2)-class BB(17) champion. Not yet reviewed by the bbchallenge community. |
| Steps | Not computed. |

## 1. How it works

M16_B shares rows A–H, I1 and J–M with Argon's DUMP_2552 (`BB16_fw4`, the engine of the BB(18) entry,
[`../BB18/`](../BB18/)). Read that write-up for the configuration family

    Ce_gen p a c r  =  0^∞ (10)^p 1^(a+2) [E] (10)^c 0 r        (head on the cell after the 1s, state E)

the W hierarchy (W 0 b = b + 3, W (j+1) b = (W j)^(b+1)(2)), the c-counter `Kc` (`CE_EVEN`, f_ω when iterated) and
the Kd1 step (two 1s of the tail, f_(ω+1)). The lemmas are re-proved for this table in `BB16_halt_fw3.v`, and they
are all parametric in the tail r. The engine reads the tail as a program:

- `1 1 r` → `r`: one Kd1 step, f_(ω+1) (`Kd1_step_all`);
- `0 r` → `1 r`: the reload `D1_cycle` (a reload followed by a/2 + 1 Kd1 steps), f_(ω+2) (`D1_cycle_all`);
- `1 0 1 0 r` → `1 0 r`: one Kd2 step (a Kc loop, a Kd1 step and a D1 cycle), f_(ω+2) (`Kd2_step_all`);
- `1 0 0 1 0 0 r` → `r`: the bridge, two W applications at the current level (`Bridge_all`);
- `1` followed by blanks: the halt (`HALT_step`).

The changed rows I0, N, O and P are where these patterns are told apart. After E and F have crossed a 1, I0 now
writes 0 and moves to N, and N, O and P read the next cells. In BB16_fw4 these states ran a reflection pass that
repeats forever. In M16_B there is no reflection: the computation consumes one finite program, written by the
opening, and halts when it runs out. The halt reads a lone 1 followed by blanks: E writes 1 at h, F crosses the 1
at h + 1, I0 writes 0 at h + 2, N0 moves on to h + 4, O0 writes 1 there and steps back, and P reads the 0 at h + 3:
P0 is the halt, 5 steps after the configuration `Ce_gen p a 0 (1)`.

## 2. The run

The opening writes the program `(10)^10 0 1 0 0 1^228` and starts at level 26:

| phase | what runs | result |
|---|---|---|
| opening | 37 steps, two W blocks, a reload: `Ce_gen 0 4 0 (1^230)` [`init_ce0`]; then 38 + 131 literal steps, a W_2 cascade, `E_1100`, `CE_EVEN` [`start_boot`] | pa_0 = `Ce_gen 26 (W_21(1)) 0 ((10)^10 0 1 0 0 1^228)` [`init_ce`] |
| level 3 | 9 Kd2 steps on (10)^9 | pa_9 = `Kd2_iter 9 pa_0`, tail `1 0 0 1 0 0 1^228` [`Kd2_loop`] |
| bridge | `Bridge_all` | pa_br = (p + 1, W_p(W_p(a + 2))), tail `1^228` |
| level 2 | 114 Kd1 steps | pa_10 = `Kd1_iter 114 pa_br`, tail blank [`Kd1_loop`] |
| last cycle | one D1 cycle on the blank: `0 → 1` | pa_11 = `D1_cycle pa_10`, tail `1` [`D1_cycle_all`] |
| halt | E, F, I, N, O, then P reads 0 | `c_end` pa_11 [`HALT_step`, `run_to_end`, `halt`] |

The halting tape is 0^∞ (10)^p 1^(a+2) 1 1 0 [P on 0] 1 0^∞ with (p, a) = pa_11. That holds p + a + 5 ones
(`ones_c_end`, `score_exact`).

**Size** (`BB16_halt_fw3.v`, from "Fast-Growing Hierarchy" on). `ok_pa n (p, a)` says n ≤ p − 5 and 4n + 6 ≤ a.
The start satisfies ok_pa 9 pa_0 (`ok_pa_0`: p = 26, a = W_21(1)). Each Kd2 step maps ok_pa n to ok_pa f_(ω+2)(n)
(`Kd2_step_dom`), so 9 of them give f_(ω+2)^9(9) = f_(ω+3)(9) (`Kd2_iter_dom`). The bridge keeps the bound
(`Bridge_dom`), the 114 Kd1 steps only raise it (`Kd1_iter_dom`), and the last D1 cycle is one more f_(ω+2)
(`D1_cycle_dom`). So f_(ω+2)(f_(ω+3)(9)) ≤ p − 5 at the halt (`halt_f_omega3`), and f_(ω+2)(f_(ω+3)(9)) < N
(`sigma_lower_bound`).

## 3. Verification

[`verify/`](verify/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about a minute, built in CI (job
`bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above (32 checks
generated from the string) and the blank start configuration. It prints the definitions the statements use and
confirms that `halt`, `halt_f_omega3`, `score_exact` and `sigma_lower_bound` are closed under the global context.

[`tools/bb16_writeup_chk.py`](tools/bb16_writeup_chk.py) simulates the machine string cell by cell, without the Coq
files. It checks the opening up to `Ce_gen 0 4 0 (1^230)` (21854 steps), the 38-step `start_38` on four tails, and
the halt on nine instances. The rest of the run is too large to simulate: a_0 = W_21(1) is already astronomically large.

## 4. Comparisons (an argument, not a Coq lemma)

The comparisons below are arguments on paper. No Coq lemma compares this machine with another entry: M14b and the
BB(17) champion have no proved upper bounds.

- f_(ω+2)(f_(ω+3)(9)) = f_(ω+2)(f_(ω+2)^9(9)) = f_(ω+2)^10(9).
- **M14b** ([`../BB14/`](../BB14/), BB(14) entry): proved σ > f_(ω+2)^9(f_(ω+1)(f_(ω+1)(3))). Since
  f_(ω+2)(9) = f_(ω+1)^9(9) > f_(ω+1)(f_(ω+1)(3)), we get f_(ω+2)^10(9) > f_(ω+2)^9(f_(ω+1)(f_(ω+1)(3))): M16_B's proved
  lower bound is above M14b's. Comparing scores would need an upper bound for M14b, which is not proved.
- **BB(17) champion** (Jacobzheng, wiki bound f_(ω+2)(f_(ω+1)^2(f_ω^2(60)))): its analysis gives one final
  f_(ω+2) run of an accumulator-sized counter, so its score is f_(ω+2)-class, below f_(ω+2)^10(9).
- **BB18_fw3** ([`../BB18/`](../BB18/)): its proved f_(ω+3)(114) = f_(ω+2)^114(114) stays above M16_B's bound.
- Not yet reviewed by the bbchallenge community.

## 5. Relation to other entries

- BB16_fw4 (DUMP_2552, Argon): the same engine, rows A–H, I1, J–M. It never halts; BB18_fw3 makes it halt with two
  added states. M16_B instead rewrites I0 and the three reflection states into a finite program and a halt, which
  keeps it at 16 states at the price of a fixed 9 at level 3 (BB18_fw3's level-3 count is the stack size, at
  least 233).
- Rows A–E and J–L also appear in M13 ([`../BB13/`](../BB13/), the previous BB(13) entry, Argon's).

## Credit

Found and proved in Coq by Argon (a Google Gemini model run by the repository owner in Google's Antigravity): the
machine, `BB16_halt_fw3.v` with `halt` and `halt_f_omega3`. The file reached this project on 2026-10-29; how the
machine was found is not recorded. This project added the score theorems (`ones`, `score_exact`,
`sigma_lower_bound`), the probe, the literal checker and the packaging, and re-checked the proofs (busycoq
`check.py`, `Print Assumptions`, the probe).
