# M16_C: M16_B with one transition changed

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RO0LO_1LP0LE_1RZ1LI

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
| I | 0RN | 0LE |                                                        |
| J | 1LA | 1LE |                                                        |
| K | 0LL | 1LB |                                                        |
| L | 0RM | 1LL |                                                        |
| M | 1LF | 1RH |                                                        |
| N | 0RO | 0LO |                                                        |
| O | 1LP | 0LE | O1 changed (M16_B: `1RM`)                              |
| P | 1RZ | 1LI | P0 is the halt                                         |

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB16_M16c_fw3.halt`. |
| Exact score | Machine-checked formula: N = p + a + 5 ones at the halt, where (p, a) = `pa_16` is given by the recursion of section 2 (`score_exact`). The halt P0 = `1RZ` is read on a 0, so σ = N + 1 = p + a + 6. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+2)(f_(ω+1)^114(f_(ω+2)^3(f_(ω+3)(9)))) < N (`sigma_lower_bound`, `sigma_bound`), hence f_(ω+2)^4(f_(ω+3)(9)) < N (`sigma_bound_simple`). |
| Comparisons | **Argument, not a Coq lemma** (section 5): above M16_B's proved lower bound, but **below the proved lower bound of the 14-state M14d_18** ([`../BB14/`](../BB14/)), and below M17_B's ([`../BB17/`](../BB17/)). Not yet reviewed by the bbchallenge community. |
| Steps | Not computed. |

## 1. The change

M16_C is M16_B (the previous entry, [`1LB1LA_..._1LP1RM_1RZ1LI.md`](1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RO0LO_1LP1RM_1RZ1LI.md))
with O1 changed from `1RM` to `0LE`. Read the M16_B write-up for the engine: the configuration family

    Ce_gen p a c r  =  0^∞ (10)^p 1^(a+2) [E] (10)^c 0 r        (head on the cell after the 1s, state E)

the W hierarchy, the c-counter `Kc`, and the tail read as a program:

- `1 1 r` → `r`: one Kd1 step, f_(ω+1) (`Kd1_step_all`);
- `0 r` → `1 r`: a D1 cycle (a reload followed by a/2 + 1 Kd1 steps), f_(ω+2) (`D1_cycle_all`);
- `1 0 1 s` → `1 s`: one Kd2 step (a Kc loop, a Kd1 step and a D1 cycle), f_(ω+2) (`Kd2_step_all`);
- `1` followed by blanks: the halt (`HALT_step`, 5 steps, P reads 0).

In the run, O1 is read only when the tail starts with `1 0 0 1` (the literal checker of section 4 finds it read once
per bridge instance and in none of the other macro steps). E writes 1, F crosses the first 1, I0 and N0 pass the two
0s, and O reads the second 1. In M16_B, O1 = `1RM` started M16_B's bridge (`1 0 0 1 0 0 r` → `r`, two W applications).
In M16_C, O1 = `0LE` erases that 1 and steps back into E. The next six transitions (E0, F0, G1, M0, F1, I1) put the
cells back to `1 0 0 1` and leave E on the tail's first 1. After these 11 steps the configuration is exactly the one
that the tail `1 1 0 1 r` reaches after 3 steps (there I1 = `0LE` erases the second 1 at once): the start of the
leftward E/J sweep of an ordinary Kd1 step. So M16_C reads `1 0 0 1 r` as `1 1 (0 1 r)`:

- `1 0 0 1 r` → `0 1 r`: one Kd1 step that leaves `0 1` in front of r (the "O1=0LE bridge": `C_REL_M16C_aux`,
  `C_REL_M16C_full`, `Bridge_M16C_all`).

The leftover `0 1` is new program: a D1 cycle and then a Kd1 step.

## 2. The run

The opening and level 3 are M16_B's (O1 is not read there; `BB16_M16c_fw3.v` re-proves them for this table). The
opening writes the program `(10)^10 0 1 0 0 1^228` and starts at level 26:

| phase | what runs | result |
|---|---|---|
| opening | 21854 steps to `Ce_gen 0 4 0 (1^230)` [`init_ce0`]; then `start_boot` | pa_0 = `Ce_gen 26 (W_21(1)) 0 ((10)^10 0 1 0 0 1^228)` [`init_ce`] |
| level 3 | 9 Kd2 steps on (10)^9 | pa_9 = `Kd2_iter 9 pa_0`, tail `1 0 0 1 0 0 1^228` [`Kd2_loop`] |
| bridge | `1 0 0 1` read as `1 1`: one Kd1 step | pa_10 = `Kd1_step pa_9`, tail `0 1 0 0 1^228` [`Bridge_M16C_all`] |
| D1 cycle | `0` → `1` | pa_11 = `D1_cycle pa_10`, tail `1 1 0 0 1^228` [`D1_cycle_all`] |
| Kd1 step | `1 1` | pa_12 = `Kd1_step pa_11`, tail `0 0 1^228` [`Kd1_step_all`] |
| D1 cycle | `0` → `1` | pa_13 = `D1_cycle pa_12`, tail `1 0 1^228` [`D1_cycle_all`] |
| Kd2 step | `1 0 1 s` → `1 s` with s = 1^227 | pa_14 = `Kd2_step pa_13`, tail `1^228` [`Kd2_step_all`] |
| level 2 | 114 Kd1 steps | pa_15 = `Kd1_iter 114 pa_14`, tail blank [`Kd1_loop`] |
| last cycle | one D1 cycle on the blank: `0` → `1` | pa_16 = `D1_cycle pa_15`, tail `1` [`D1_cycle_all`] |
| halt | E, F, I, N, O, then P reads 0 | `c_end` pa_16 [`HALT_step`, `run_to_end`, `halt`] |

Where M16_B turned `1 0 0 1 0 0` into one bridge and went straight to the 114 Kd1 steps, M16_C runs Kd1, D1, Kd1,
D1, Kd2 on the same cells: three more f_(ω+2) steps (two D1 cycles and a Kd2 step). The Kd2 step borrows the first 1
of `1^228` and gives it back, so the 114 Kd1 steps and the final D1 cycle are as in M16_B.

The halting tape is 0^∞ (10)^p 1^(a+2) 1 1 0 [P on 0] 1 0^∞ with (p, a) = pa_16. That holds p + a + 5 ones
(`ones_c_end`, `score_exact`).

## 3. Size

(`BB16_M16c_fw3.v`, from "Fast-Growing Hierarchy" on.) `ok_pa n (p, a)` says n ≤ p − 5 and 4n + 6 ≤ a. The start
satisfies ok_pa 9 pa_0 (`ok_pa_0`). Each Kd2 step and each D1 cycle maps ok_pa n to ok_pa f_(ω+2)(n)
(`Kd2_step_dom`, `D1_cycle_dom`); a Kd1 step maps it to ok_pa f_(ω+1)(n) (`Kd1_step_dom`, `Kd1_iter_dom`). Along the
run:

| after | bound n with ok_pa n |
|---|---|
| level 3 (pa_9) | f_(ω+2)^9(9) = f_(ω+3)(9) =: N0 |
| bridge, D1 cycle (pa_11) | f_(ω+2)(N0) (the bridge's f_(ω+1) is not used) |
| Kd1 step, D1 cycle (pa_13) | f_(ω+2)^2(N0) (the Kd1 step's f_(ω+1) is not used) |
| Kd2 step (pa_14) | f_(ω+2)^3(N0) |
| 114 Kd1 steps (pa_15) | f_(ω+1)^114(f_(ω+2)^3(N0)) |
| last D1 cycle (pa_16) | f_(ω+2)(f_(ω+1)^114(f_(ω+2)^3(N0))) |

So f_(ω+2)(f_(ω+1)^114(f_(ω+2)^3(f_(ω+3)(9)))) ≤ p − 5 at the halt (`halt_f_omega3`) and is < N (`sigma_bound`,
`sigma_lower_bound`). Dropping the 114 Kd1 steps gives f_(ω+2)^4(f_(ω+3)(9)) < N (`sigma_bound_simple`).

## 4. Verification

[`verify_m16c/`](verify_m16c/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 30 s, built in CI (job
`bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above (32 checks generated
from the string) and the blank start configuration. It prints the definitions the statements use and confirms that
`halt`, `halt_f_omega3`, `score_exact`, `sigma_bound`, `sigma_bound_simple` and `sigma_lower_bound` are closed under
the global context. Argon's file is used as received, except that its closing `Print Assumptions` lines moved to the
probe and `sigma_lower_bound` (a restatement of `sigma_bound` with `<`) was appended; see the verify README.

[`tools/m16c_writeup_chk.py`](tools/m16c_writeup_chk.py) simulates the machine string cell by cell, without the Coq
files. It checks the opening up to `Ce_gen 0 4 0 (1^230)` (21854 steps, O1 and P0 not read), `start_38`, the bridge
(`C_REL_M16C_aux` on 27 instances; `C_REL_M16C_full` next to the ordinary `C_REL_full` on 18 instances, same numbers
with tail `0 1 r` instead of `r`; the 11-step / 3-step coincidence above on 12 instances; and that under M16_B's
O1 = `1RM` the same instance does not give this result), the macro steps `CE_EVEN`, `D1_REL` and `D2_STEP_full` on
small instances, and the halt on nine instances. O1 is read exactly once in each bridge instance and never in the
others. The rest of the run is too large to simulate: a_0 = W_21(1) is already astronomically large.

## 5. Comparisons (an argument, not a Coq lemma)

These compare proved lower bounds. None of the machines below has a proved upper bound, so none of this says how the
true scores compare.

- **M16_B** (previous BB(16) entry): proved f_(ω+2)(f_(ω+3)(9)) = f_(ω+2)^10(9) < N. M16_C's proved
  f_(ω+2)^4(f_(ω+3)(9)) = f_(ω+2)^13(9) is above it. The two runs agree up to pa_9.
- **M14d_18** (`1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LN1LK_1RZ0LH_0LG1LJ`,
  the BB(14) entry, [`../BB14/`](../BB14/)): proved f_(ω+2)^17(f_(ω+1)^2(3)) < its score. **That is above M16_C's
  proved bound.** For y ≥ 114, f_(ω+1)^114(y) ≤ f_(ω+1)^y(y) = f_(ω+2)(y), so M16_C's bound is at most
  f_(ω+2)^5(f_(ω+3)(9)) = f_(ω+2)^14(9); and f_(ω+1)^2(3) > 9, so f_(ω+2)^17(f_(ω+1)^2(3)) > f_(ω+2)^14(9). Since
  BB(n+1) ≥ BB(n) + 1 (send the halt to a new state that runs right over 1s and halts on the first 0, writing 1),
  BB(16) ≥ BB(14) + 2, and this gives a better proved lower bound for BB(16) than M16_C's own proved bound. M16_C's
  true score is not proved smaller than M14d_18's.
- **M17_B** ([`../BB17/`](../BB17/)): proved f_(ω+3)^3(9) < N, above f_(ω+2)^14(9) and so above M16_C's bound.
- The bbchallenge wiki's BB(16) row (checked 2026-11-04) is M16_B. M16_C has not yet been reviewed by the
  bbchallenge community.

## Credit

Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity (2026-11-03):
the machine and `BB16_M16c_fw3.v` with `halt`, `halt_f_omega3`, `score_exact`, `sigma_bound` and
`sigma_bound_simple`. Re-checked here: `sigma_lower_bound` (a restatement), the probe, the literal checker and the
packaging (busycoq `check.py`, `Print Assumptions`, the probe).
