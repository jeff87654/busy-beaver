# BB18_fw3: an 18-state machine at level f_(ω+3)

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_1RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RQ0RG_0LG1LP_0LO1LP_1LQ0RR_1RZ0LP

|   | 0   | 1   |                                                              |
|---|-----|-----|--------------------------------------------------------------|
| A | 1LB | 1LA |                                                              |
| B | 1RC | 0LA |                                                              |
| C | 1RD | 1RC |                                                              |
| D | 1RE | 1RK |                                                              |
| E | 1RF | 0LJ |                                                              |
| F | 1LG | 1RI |                                                              |
| G | 1RM | 0LM |                                                              |
| H | 1LG | 0RC |                                                              |
| I | 1RN | 0LE |                                                              |
| J | 1LA | 1LE |                                                              |
| K | 0LL | 1LB |                                                              |
| L | 0RM | 1LL |                                                              |
| M | 1LF | 1RH |                                                              |
| N | 0RQ | 0RG | N0 goes to Q (BB16_fw4: `0LP`); read only when a pass starts |
| O | 0LG | 1LP |                                                              |
| P | 0LO | 1LP |                                                              |
| Q | 1LQ | 0RR | new: plants the marker / finds it                            |
| R | 1RZ | 0LP | new: R0 is the halt                                          |

Rows A–P are the table of DUMP_2552 (`BB16_fw4`), a 16-state machine of Argon's that never halts, except N0.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB18_fw3.halt`. |
| Exact score | Machine-checked formula: N = p + a + 5 ones at the halt, where (p, a) = `Kpass1 pa_init` is the pair after the opening and one pass (`score_exact`). The halt R0 = `1RZ` is read on a 0, so σ = N + 1 = p + a + 6. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+2)(f_(ω+3)(114)) < N (`sigma_lower_bound`), so f_(ω+3)(114) < N (`sigma_lower_bound_fw3`). |
| Comparisons | **Argument, not a Coq lemma** (section 4): f_(ω+3)(114) = f_(ω+2)^114(114) is far above M14b's proved f_(ω+2)^9(f_(ω+1)(f_(ω+1)(3))) and the f_(ω+2)-class BB(17)/BB(18) champions. Not yet reviewed by the bbchallenge community. |
| Steps | Not computed. |

## 1. How it works

### The engine (Argon's BB16_fw4)

DUMP_2552 is a 16-state machine found by Argon (a Google Gemini model run by the repository owner). Its Coq file,
`BB16_fw4.v`, proves that it never halts and that it grows at level f_(ω+4). All of its lemmas except one are reused
here unchanged, re-proved for this table in `BB18_fw3.v`. They work on the configuration family

    Ce_gen p a c r  =  0^∞ (10)^p 1^(a+2) [E] (10)^c 0 r        (head on the cell after the 1s, state E)

and are all parametric in the right tail r, so the machine never reads r. Inside, the C/A/H cascades compute a
hierarchy W (`W 0 b = b + 3`, `W (j+1) b = (W j)^(b+1)(2)`, so W_j ≈ f_j), and there are four nested counter
levels:

- `Kc` (`CE_EVEN`): one (10) token of c turns the level p into p + a/2 and the accumulator a into W_(p−1)(1).
  Iterated, that is f_ω.
- `Kd1_step` (`D1_STEP_*`): two 1s of the tail are consumed; this restarts a Kc loop of about a/2 tokens, so each
  step is f_(ω+1) (`Kd1_step_dom`).
- the reload `D1_REL_gen`: a 0 in the tail becomes a block of a + 3 ones, which the Kd1 steps then consume.
  So a tail `0 r` becomes `1 r` (`Krel_odd`), and `0 1^(2k+1) r` becomes `r` (`Krel_even`).
- `Kd2_step` = `Krel_even 0`: one (01) of the tail; iterated, f_(ω+2) per step (`Kd2_step_dom`).

**The pass.** At a pass boundary `Ce_gen p a 0 (1 0 0 …)` the machine reflects the whole stack (`P_DUMP_raw`).
E, F and I write 1s, then N0 hands over to P, which walks left over the entire tape. At the left end, P_BOOT (a fixed
141-step gadget, `P_BOOT_141`) starts a fresh level, and the old stack now lies to the right as a tail of p − 4
(01) tokens. `Kd2_loop` eats them: p − 4 applications of an f_(ω+2) map, which is f_(ω+3)-sized
(`iter_f_omega2_ge_f_omega3`). The reload then turns the remaining block into a new seed. In BB16_fw4 the tail is
then `1` followed by blanks again, so the pass repeats forever (non-halting, f_(ω+4) overall).

### The change: a two-state counter on N0

N0 is read only at the start of a pass. In the opening, N is always entered on a 1, and P_BOOT reads N1 but never N0.
In BB18_fw3, N0 runs a routine through the new states Q and R. With h the head cell of the boundary configuration,
and the seed 1 at h + 1, the first pass starts like this:

| step | state, cell | reads | writes, moves |
|---|---|---|---|
| E, F, I | h, h+1, h+2 | 0, 1, 0 | 1s (as in BB16_fw4), then N at h+3 |
| N | h+3 | 0 | 0, right, Q |
| Q | h+4 | 0 | 1 (the marker), left, Q |
| Q | h+3 | 0 | 1, left, Q |
| Q | h+2 | 1 | 0 (erases I's 1), right, R |
| R | h+3 | 1 | 0, left, P |
| P, O | h+2, h+1 | 0, 1 | P0 → O, O1 → P: P is at h and walks left as in BB16_fw4 |

The tape to the right of h is now `1 0 0 1` (`P_DUMP_raw`: the reflected tail is (10)^p 1^(a+4) 0 0 1 instead of
(10)^p 1^(a+5)). The whole pass then runs as in BB16_fw4. Because the last block is now even (a + 4 ones), it is
reloaded by `Krel_x` (`Krel_x_all`: `0 1^(2k) r` becomes `1 r`). The next boundary is at the **same** head position,
since I's 1 was erased, and the marker is still at h + 4:

    Ce_gen p a 0 (1 0 0 …)  →+  Ce_gen p' a' 0 (1 0 0 1)        (p', a') = Kpass1 (p, a)      [Kpass1_all]

At the start of pass 2, E, F, I and N run as before, Q reads the marker at h + 4 and moves right to R, and R reads 0
at h + 5: that is the halt, 6 steps after the boundary (`HALT_step`).

## 2. The run

| phase | what runs | result |
|---|---|---|
| opening | 37 steps, two W blocks, a reload, 116 steps, `CE_EVEN` | `Ce_gen 5 38 0 (1^228)` [`init_ce`] |
| bootstrap | `Kd1_loop` 114 times, `Krel_odd` | boundary 1: `Ce_gen p a 0 (1)` with p ≥ 233 [`init_pass`] |
| pass 1 start | E, F, I, then the N0 routine (10 steps) | marker planted, P walks left [`P_DUMP_raw`] |
| pass 1 | P_BOOT, `pa_dump0` = 22 Kd1 steps, `Kd2_loop` (p − 4 tokens), `Krel_x` | boundary 2: `Ce_gen (Kpass1 pa_init) 0 (1 0 0 1)` [`Kpass1_all`] |
| pass 2 start | E, F, I, N, Q, R | halt in R reading 0 [`HALT_step`, `halt`] |

The halting tape is 0^∞ (10)^p 1^(a+2) 1 1 1 0 0 0^∞ with (p, a) = `Kpass1 pa_init`, which holds p + a + 5 ones
(`ones_c_end`, `score_exact`).

**Size** (`BB18_fw3.v`, section "Score"). The level after the bootstrap is at least 233 (`init_pass`). The Kd2 loop
of pass 1 runs p − 4 ≥ 2·114 times from a start with level ≥ 1 (`pa_dump0_dom`), which gives f_(ω+3)(114)
(`Kd2_iter_dom`, `iter_f_omega2_ge_f_omega3`). `Krel_x` adds one more f_(ω+2) (`Krel_x_dom`), so
f_(ω+2)(f_(ω+3)(114)) < N (`Kpass1_dom`, `sigma_lower_bound`). The argument 114 comes only from the bound p ≥ 233 on
boundary 1. On paper, the real level there is itself f_(ω+2)-class (114 Kd1 steps and a reload), so σ is roughly
f_(ω+3) of an f_(ω+2)-class number. That is not proved and not needed.

## 3. Verification

[`verify/`](verify/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 40 s, built in CI (job
`bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above (36 checks generated
from the string) and the blank start configuration. It prints the definitions the statements use and confirms that
`halt`, `score_exact`, `sigma_lower_bound` and `sigma_lower_bound_fw3` are closed under the global context.

[`tools/bb18_writeup_chk.py`](tools/bb18_writeup_chk.py) simulates the machine string cell by cell, without the Coq
files. It checks that the opening never reads N0, Q or R in its first 10^7 steps, that P_BOOT reads N1 but not N0,
and the pass-start routine and the halt on 20 concrete instances `Ce_gen p a 0 ·`.

## 4. Comparisons (an argument, not a Coq lemma)

The comparisons below are arguments on paper. No Coq lemma compares this machine with another entry: M14b and the
BB(17)/BB(18) champions have no proved upper bounds to compare against.

- f_(ω+3)(114) = f_(ω+2)^114(114), by the definition f_(ω+3)(n) = f_(ω+2)^n(n).
- **M14b** ([`../BB14/`](../BB14/), BB(14) entry): proved σ > f_(ω+2)^9(f_(ω+1)(f_(ω+1)(3))). Its run is
  thirteen phases, nine of which are f_(ω+2) rounds (its write-up, section 2). We expect its score to be below a
  few more iterations of f_(ω+2), far below f_(ω+2)^114(114), but M14b has no proved upper bound, so this is not
  proved. Through BB(n+1) ≥ BB(n), the same comparison covers the BB(15)–BB(17) lower bounds.
- **BB(17)/BB(18) champions** (Jacobzheng; wiki bounds f_(ω+2)(f_(ω+1)^2(f_ω^2(60))) and
  f_(ω+2)(f_(ω+1)^3(f_ω^2(60)))): their analysis gives one final f_(ω+2) run of an accumulator-sized counter, so
  their scores are f_(ω+2)-class. f_(ω+2)^2(114) is already above f_(ω+2)(f_(ω+1)^3(f_ω^2(60))).
- The bound is not yet reviewed by the bbchallenge community.

## 5. Relation to other entries

- Rows A–E and J–L are the same as in M13 ([`../BB13/`](../BB13/), the previous BB(13) entry, also Argon's), so
  this is the same engine family as M12–M14b.
- BB16_fw4, the 16-state engine, never halts. Its Coq file proves f_(ω+3) growth per pass and f_(ω+4) over the
  infinite run. It is not a busy beaver result on its own.
- With one state (17 states), no routine on N0 was found: a search over all one-state routines (in the same
  lemma-based model of the right end of the tape) found none that halts after a full pass.

## Credit

Engine: Argon (a Google Gemini model run by the repository owner in Google's Antigravity), DUMP_2552 and its Coq
file `BB16_fw4.v`. The 18-state halter (the N0 counter routine), its search and the Coq proof (`BB18_fw3.v`,
generated from `BB16_fw4.v` with the engine lemmas unchanged): this project, 2026-10-29, the repository owner with
Claude models (Anthropic) as agents.
