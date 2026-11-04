# M19_fw4: a 19-state machine at level f_(ω+4)

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_1RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0RG_0LG1LP_0LO1LP_1LS0RR_1RZ0LP_0LR1LS

|   | 0   | 1   |                                                                        |
|---|-----|-----|------------------------------------------------------------------------|
| A | 1LB | 1LA |                                                                        |
| B | 1RC | 0LA |                                                                        |
| C | 1RD | 1RC |                                                                        |
| D | 1RE | 1RK |                                                                        |
| E | 1RF | 0LJ |                                                                        |
| F | 1LG | 1RI |                                                                        |
| G | 1RM | 0LM |                                                                        |
| H | 1LG | 0RC |                                                                        |
| I | 1RN | 0LE |                                                                        |
| J | 1LA | 1LE |                                                                        |
| K | 0LL | 1LB |                                                                        |
| L | 0RM | 1LL |                                                                        |
| M | 1LF | 1RH |                                                                        |
| N | 1RQ | 0RG | N0 goes to Q (BB16_fw4: `0LP`); read only when a pass starts           |
| O | 0LG | 1LP |                                                                        |
| P | 0LO | 1LP |                                                                        |
| Q | 1LS | 0RR | new: Q0 starts the parking walk, Q1 erases a parked 1                  |
| R | 1RZ | 0LP | new: R1 erases one 1 and hands over to P; R0 is the halt               |
| S | 0LR | 1LS | new: walks left over the accumulator block without changing it        |

Rows A–P are the table of DUMP_2552 (`BB16_fw4`), a 16-state machine of Argon's that never halts, except N0.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB19_halt_fw4.halt`. |
| Exact score | Machine-checked formula: N = p + a + 6 ones at the halt, where (p, a) = `pa_final` = `Kcycle pa_init` is the pair after the opening and the last pass (`score_exact`). The halt R0 = `1RZ` is read on a 0, so σ = N + 1 = p + a + 7. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+4)(f_(ω+2)(114)) < N (`sigma_lower_bound`), so f_(ω+4)(114) < N (`sigma_lower_bound_fw4`). |
| Comparisons | **Argument, not a Coq lemma** (section 4): above the proved bound f_(ω+3)^4(9) of M18_4round, the BB(18) entry, and so above the smaller entries here. **Not a BB(19) record** (corrected 2026-11-04): the wiki's BB(19) champion (Jacobzheng, > f_(ω+7)^2(5)) is far larger. Not yet reviewed by the bbchallenge community. |
| Steps | Not computed. |

## 1. How it works

### The engine (Argon's BB16_fw4)

The engine is the same as in BB18_fw3, the previous BB(18) entry; its write-up
([`../BB18/`](../BB18/), section 1) describes it in more detail. All engine lemmas are re-proved for this table in
`BB19_halt_fw4.v`. They work on the configuration family

    Ce_gen p a c r  =  0^∞ (10)^p 1^(a+2) [E] (10)^c 0 r        (head on the cell after the 1s, state E)

and are all parametric in the right tail r, so the machine never changes r. Below, c = 0 always. Seen from the right
end of the tape, the engine has three moves:

- `Kd1_step_all`: a tail `1 1 u` becomes `u`. This is one f_(ω+1) step on the pair (p, a).
- the reload `D1_REL_gen`: a 0 in the tail becomes a block of a + 3 ones, which Kd1 steps then eat in pairs. Since a
  is always even, a tail `0 u` becomes `1 u` (`Krel_odd_all`), `0 1^(2k) u` becomes `1 u` (`Krel_x_all`), and
  `0 1 u` becomes `u` (`Kd2_step_all`, an f_(ω+2) step).
- **the pass**, at a tail `1 0 0 …`. E, F and I write 1s and N reads a 0. In BB16_fw4, N0 hands over to P, which
  walks left over the whole tape and reflects the stack (10)^p. At the left end, P_BOOT (a fixed 141-step gadget,
  `P_BOOT_141`, then `CE_EVEN` and a reload) starts a fresh level, 22 Kd1 steps eat 44 ones (`pa_dump0`), and
  `Kd2_loop` eats the reflected stack as (01) tokens. That is about p f_(ω+2) steps, so f_(ω+3) per pass
  (`iter_f_omega2_ge_f_omega3`). A reload then makes the next boundary.

In BB16_fw4 every pass ends at a tail `1 0 0 …` again, so it never halts.

### The change: accumulator parking

N0 is read only at the start of a pass. In the opening, N is always entered on a 1, and P_BOOT reads N1 but never N0.
In this machine N0 enters three new states Q, R and S. The pass start then depends on the cell at h + 4, where h is
the head cell of the boundary configuration.

**Pass 1: parking.** Here the tail is `1` followed by blanks (`SEED_c1_raw`):

| step | state, cell | reads | writes, moves |
|---|---|---|---|
| E, F, I | h, h+1, h+2 | 0, 1, 0 | 1s (as in BB16_fw4), then N at h+3 |
| N | h+3 | 0 | 1, right, Q |
| Q | h+4 | 0 | 1, left, S. The block of ones is now 1^(a+7), from h−a−2 to h+4 |
| S | h+3 down to h−a−2 | 1, a + 6 times | 1, left, S: crosses the block without changing it |
| S | h−a−3 | 0 (the 0 of the last (10) pair of the stack) | 0, left, R |
| R | h−a−4 | 1 (the 1 of that pair) | 0 (erases it), left, P |
| P, O | | | P walks left over the rest of the stack, (10)^(p−1), as in BB16_fw4 |

To the right of the left end, the tape is now (10)^(p−1) 0 0 1^(a+7). The pass then runs as in BB16_fw4, but the
broken pair stops `Kd2_loop` early: it eats p − 5 tokens, and the reload `Krel_odd` turns the 0 in front of `0 0`
into a 1. The block 1^(a+7) is left in place, to the right, as a unary pass counter:

    Ce_gen p a 0 (1 0 0 …)  →+  Ce_gen p₁ a₁ 0 (1 0 0 1^(a+7) 0 …)     (p₁, a₁) = Kseed (p, a)     [Kseed_c1_all]

with `Kseed (p, a) = Krel_odd (Kd2_iter (p − 5) pa_dump0)` (the pass start up to `pa_dump0` is `SEED_c1_boot`).
The new boundary is a + 6 cells left of the old one.

**Passes 2, 3, …: countdown.** Now the tail is `1 0 0 1 1 r` (`CD_DUMP_raw`):

| step | state, cell | reads | writes, moves |
|---|---|---|---|
| E, F, I | h, h+1, h+2 | 0, 1, 0 | 1s, then N at h+3 |
| N | h+3 | 0 | 1, right, Q |
| Q | h+4 | 1 (first parked 1) | 0, right, R |
| R | h+5 | 1 (second parked 1) | 0, left, P |
| P | h+4 | 0 | 0, left, O |
| O | h+3 | 1 | 1, left, P: P walks left over 1^(a+6) and the stack, as in BB16_fw4 |

The tape right of the left end is now (10)^p 1^(a+6) 0 0 r: two parked 1s are gone. The pass runs as in BB16_fw4
(`Kd2_loop` with p − 4 tokens), and since a + 6 is even, `Krel_x` turns `0 1^(a+6)` into `1`:

    Ce_gen p a 0 (1 0 0 1^(d+2) u)  →+  Ce_gen p' a' 0 (1 0 0 1^d u)     (p', a') = Kcd_step (p, a)     [Kcd_step_all]

with `Kcd_step (p, a) = Krel_x (a/2 + 3) (Kd2_iter (p − 4) pa_dump0)`. The tail r is not touched, so the next
boundary is 2 cells to the right. `Kcd_loop` iterates this: m countdown passes remove 2m parked 1s.

**The count.** After pass 1 there are a₀ + 7 = 2(a₀/2 + 3) + 1 parked 1s, where a₀ (even) is the accumulator at the
start of pass 1. So `Kcycle1_all` runs a₀/2 + 3 countdown passes and stops with one parked 1:

    Ce_gen p a 0 (1 0 0 …)  →+  Ce_gen (Kcycle (p, a)) 0 (1 0 0 1 0 …)     Kcycle pa = Kcd_iter (a/2 + 3) (Kseed pa)

That is a₀/2 + 4 passes in all. Each is f_(ω+3) of the level it starts from, and a₀ itself is huge, so the whole
run is f_(ω+4).

**The halt.** At the next boundary, E, F, I and N run as before, Q reads the last parked 1 at h + 4 (Q1: write 0,
move right) and R reads 0 at h + 5: that is the halt, 6 steps after the boundary, counting the halting transition
(`HALT_step`). The parking pass moved the boundary a₀ + 6 cells left and each countdown pass moves it 2 cells right, so
the halt happens next to the first boundary (cell h + 5 of pass 1). Coq does not need this fact; the checker in
section 3 confirms it on small instances.

## 2. The run

| phase | what runs | result |
|---|---|---|
| opening | 37 steps, two W blocks, a reload, 116 steps, `CE_EVEN` | `Ce_gen 5 38 0 (1^228)` [`init_ce`] |
| bootstrap | `Kd1_loop` 114 times, `Krel_odd` | boundary 1: `Ce_gen p₀ a₀ 0 (1)` with (p₀, a₀) = `pa_init`, p₀ ≥ 233, a₀ even [`init_pass`] |
| pass 1 (parking) | E, F, I, N, Q, the S walk, R, P; P_BOOT, `pa_dump0`, `Kd2_loop` (p₀ − 5 tokens), `Krel_odd` | `Ce_gen (Kseed pa_init) 0 (1 0 0 1^(a₀+7))` [`Kseed_c1_all`] |
| passes 2 to a₀/2 + 4 (countdown) | each: E, F, I, N, Q, R erase two parked 1s; P_BOOT, `pa_dump0`, `Kd2_loop` (p − 4 tokens), `Krel_x` | `Ce_gen pa_final 0 (1 0 0 1)` [`Kcd_loop`, `Kcycle1_all`] |
| halt | E, F, I, N, Q, R | halt in R reading 0 [`HALT_step`, `run_end`, `halt`] |

The halting tape is 0^∞ (10)^p 1^(a+2) 1 1 1 1 0 0 0^∞ with (p, a) = `pa_final`, the head on the second 0 after
the ones. It holds p + a + 6 ones (`ones_c_end`, `score_exact`).

**Size** (`BB19_halt_fw4.v`, the domination section). The proof tracks `ok_pa n (p, a)`, which says n ≤ p − 5 and
4n + 6 ≤ a.

- `pa_init_dom`: `ok_pa (2 · f_(ω+2)(114)) pa_init`, from the 114 Kd1 steps and the reload of the bootstrap.
- `Kseed_dom` and `Kcd_step_dom`: if `ok_pa (2n)` holds at the start of a pass, `ok_pa (2 · f_(ω+3)(n))` holds after
  it. The pass's `Kd2_loop` runs at least 2n tokens from `pa_dump0` (`pa_dump0_dom`), which gives f_(ω+3)(n)
  (`iter_f_omega2_ge_f_omega3`).
- `Kcd_iter_dom`, `Kcycle_dom`: the a/2 + 4 passes are at least n of them, so `ok_pa (2 · f_(ω+4)(n)) (Kcycle pa)`.
- `pa_final_dom`: with n = f_(ω+2)(114), a ≥ 8 · f_(ω+4)(f_(ω+2)(114)) + 6 for (p, a) = `pa_final`, so
  f_(ω+4)(f_(ω+2)(114)) < N (`sigma_lower_bound`). Then f_(ω+4)(114) < N by monotonicity (`sigma_lower_bound_fw4`).

The bound is loose: the proof counts only n of the a₀/2 + 4 ≥ 4n + 7 passes. A sharper bound is not needed.

## 3. Verification

[`verify/`](verify/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 40 s, built in CI (job
`bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above (38 checks generated
from the string) and the blank start configuration. It prints the definitions the statements use and confirms that
`halt`, `score_exact`, `sigma_lower_bound` and `sigma_lower_bound_fw4` are closed under the global context.

[`tools/bb19_writeup_chk.py`](tools/bb19_writeup_chk.py) simulates the machine string cell by cell, without the Coq
files. It checks:

1. the opening never reads N0, Q, R or S in its first 10^7 steps (and never goes right of cell 8);
2. P_BOOT reads N1 but not N0, Q, R or S;
3. the parking pass start on 20 concrete instances `Ce_gen p a 0 (1)`: (10)^(p−1) 0 0 1^(a+7), with S reading
   a + 6 ones and one 0;
4. the countdown pass start on the same instances with five different tails r: (10)^p 1^(a+6) 0 0 r, r never visited;
5. the halt on the same instances: 6 steps from `Ce_gen p a 0 (1 0 0 1)`, in R reading 0, p + a + 6 ones;
6. the whole right end for a₀ = 4, 6, 8, 10, 20, 40: literal pass starts as in 3–5, with the middle of each pass
   replaced by the tape effect of the lemmas above. There are exactly a₀/2 + 4 passes, the boundary moves a₀ + 6
   cells left in pass 1 and 2 cells right in each later pass, and the halt is at cell h + 5 of the first boundary.

It runs in about 10 s.

## 4. Comparisons (an argument, not a Coq lemma)

The comparisons below are arguments on paper. No Coq lemma compares this machine with another entry: none of them has
a proved upper bound.

- f_(ω+4)(n) = f_(ω+3)^n(n), by the definition. Here n = f_(ω+2)(114) ≥ 114.
- **M18_4round** ([`../BB18/`](../BB18/), the BB(18) entry): proved f_(ω+3)^4(9) < σ. Since f_(ω+3) is increasing
  and x ≤ f_(ω+3)(x), and n ≥ 4, n > 9: f_(ω+3)^n(n) ≥ f_(ω+3)^4(n) > f_(ω+3)^4(9). So M19_fw4's proved bound is
  above M18_4round's.
- **M17_B** ([`../BB17/`](../BB17/), the BB(17) entry, f_(ω+2)^116(f_(ω+3)^3(9))), **BB18_fw3**
  (f_(ω+2)(f_(ω+3)(114))) and **M16_B** ([`../BB16/`](../BB16/)) have proved bounds below M18_4round's (see the main
  README), so below this one as well. The wiki's BB(17) and BB(18) champions (Jacobzheng) are f_(ω+2)-class.
- **BB(19): not a record** (corrected 2026-11-04; this write-up first said the wiki's BB(19) row was empty). The
  bbchallenge wiki's Champions page (checked 2026-11-04) lists BB(19) = Jacobzheng, > f_(ω+7)^2(5) (marked "Not
  independently verified"). That is far above anything at level f_(ω+4), so M19_fw4 says nothing new about BB(19) or
  higher. The wiki's BB(20) champion (Jacobzheng, > f_(ω·2)(f_(ω+2)^2(f_10(2)))) is larger still.
- The bound is not yet reviewed by the bbchallenge community.

## 5. Relation to other entries

- **BB18_fw3** ([`../BB18/`](../BB18/), the previous BB(18) entry): the same engine, opening and bootstrap. M19_fw4
  is BB18_fw3 with N0 `0RQ` → `1RQ`, Q0 `1LQ` → `1LS` and the new state S (`0LR 1LS`); Q1 = `0RR` and the row
  R = `1RZ 0LP` are the same. BB18_fw3 plants a fixed marker and halts at the start of pass 2. Parking turns the
  accumulator itself into the pass counter, which gives a₀/2 + 4 passes instead of one.
- **BB16_fw4**, the 16-state engine, never halts. Its Coq file (Argon) proves f_(ω+3) growth per pass and f_(ω+4)
  over the infinite run. It is not a busy beaver result on its own.
- **M16_B, M17_B, M18_4round** ([`../BB16/`](../BB16/), [`../BB17/`](../BB17/), [`../BB18/`](../BB18/)), also Argon's,
  are a different branch: their tables share rows A–H, I1 and J–M with BB16_fw4, but not I0 or the rows from N on.
- Argon's notes (not re-checked here) report a search over all routines on N0 with rows A–P fixed: fixed-marker
  counters reach at most 1 pass with 2 new states, 3 passes with 3 and 9 passes with 4, and parking needs 3 new states.
  Argon also built a 20-state variant that runs two parking cycles (f_(ω+4)^2). It is not published here, because the
  BB(20) champion is far larger.

## Credit

Engine: Argon (a Google Gemini model run by the repository owner in Google's Antigravity), DUMP_2552 and its Coq
file `BB16_fw4.v`. The 19-state halter (accumulator parking) and its Coq proof `BB19_halt_fw4.v`: Argon, 2026-11-02.
The header comment of the proof (Argon's original described a 20-state machine), the probe, this write-up, the
checker, the packaging and the re-check: this project, the repository owner with Claude models (Anthropic) as agents.
