# M18_229round: an 18-state machine at level f_(ω+3), 229 rounds

    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1LR_0RB1LI_1RZ1RR_1RN0LO

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
| N | 1RQ | 0LO |                                                                  |
| O | 1LP | 1LR | O1 changed (M18_4round: `1LN`)                                   |
| P | 0RB | 1LI |                                                                  |
| Q | 1RZ | 1RR | changed (M18_4round: `1RR 0LO`); Q0 is the halt                   |
| R | 1RN | 0LO | changed (M18_4round: `0RO 1RZ`)                                   |

Rows A–N and P are those of M18_4round ([`1LB1LA_..._1RR0LO_0RO1RZ.md`](1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1LN_0RB1LI_1RR0LO_0RO1RZ.md),
the previous BB(18) entry); rows A–P apart from O1 are those of M17_B ([`../BB17/`](../BB17/)); rows A–M and the
slots N1, O0 and P1 are those of M16_B ([`../BB16/`](../BB16/)). All are Argon's.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB18_229round_fw3.halt`. |
| Exact score | Machine-checked formula: N = p + a + 8 ones when Q reads 0 at the halt, where (p, a) = `pa_R229` is given by the recursion of section 2 (`score_exact`). The halt Q0 = `1RZ` writes 1 on that 0, so σ = N + 1 = p + a + 9. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+3)^229(9) < N, σ = N + 1 (`sigma_lower_bound`). |
| Comparisons | **Argument, not a Coq lemma** (section 4): above M18_4round's proved f_(ω+3)^4(9), and above f_(ω+4)(9). Not yet reviewed by the bbchallenge community. |
| Steps | Not computed. |

## 1. How it works

Read the M18_4round write-up first: the engine, the bounce and the round are the same here, and so are the lemmas
`Kd1_step_all`, `D1_cycle_all`, `Kd2_loop`, `Kd2_alt_loop`, `bounce_155`, `P0_bounce` and `ROUND_after_sweep`.
The configuration family is

    Ce_gen p a c r  =  0^∞ (10)^p 1^(a+2) [E] (10)^c 0 r        (head on the cell after the 1s, state E)

The opening leaves the tail `(10)^10 0 1 0 0 1^228`. M18_4round reads three round headers from this tail and never
uses the 1^227 at its end. This machine uses the 228 ones as a reservoir: every two rounds use up two of them, so
there are 1 + 228 = 229 rounds.

### The reader

With h the head cell of `Ce_gen p a 0 X` (E reading 0), E0, F1 and I0 run as in M18_4round and leave N on the cell
h + 3. N, Q and R then read the tail to the right in a loop:

- N0 = `1RQ` writes 1 on a 0, Q1 = `1RR` passes a 1, R0 = `1RN` writes 1 on a 0 and hands back to N;
- the loop stops at the first cell that does not fit: R1 = `0LO` and N1 = `0LO` clear that 1 and turn left;
- Q0 = `1RZ` is the halt: Q reads 0 only once the reservoir is empty.

After the turn, O1 = `1LR` and R1 = `0LO` walk left over the cells the reader filled, as O1 = `1LN` and N1 = `0LO`
did in M18_4round (R takes N's place; at a 0 the hop R0 = `1RN`, N1 = `0LO` does what N0 = `1RQ`, Q1 = `0LO` did
there). Over the level block and the (10)^p block the sweep then runs as in M18_4round, and P reaches the left end.

### The two sweeps

There are two round headers. For p ≥ 1 and a even:

- Odd header `1 0 0 1 0 0 1 1`: N writes 1 at h + 3, Q passes h + 4, R writes 1 at h + 5, N writes 1 at h + 6,
  Q passes the first reservoir 1 at h + 7 and R reads the second at h + 8 and clears it. After 4p + a + 22 steps:

      Ce_gen p a 0 (1 0 0 1 0 0 1 1 u)  →+  P on the left-end 0, then (10)^(p+1) 0 (10)^(a/2+2) 0 1 0 1 0 u    [SWEEP_odd]

- Even header `1 0 0 1 0 1 0` (what the odd round leaves): N writes 1 at h + 3, Q passes h + 4, R writes 1 at
  h + 5, and N reads the 1 at h + 6 and clears it. After 4p + a + 18 steps:

      Ce_gen p a 0 (1 0 0 1 0 1 0 u)    →+  P on the left-end 0, then (10)^(p+1) 0 (10)^(a/2+2) 0 1 0 0 u      [SWEEP_even]

- Header `1 0 0 1 0 0` followed by blank tape: N, Q, R, N as in the odd header, and then Q reads 0 at h + 7: the
  halt, after seven steps (`HALT_step`).

The step counts are measured by the literal checker (section 3); the Coq lemmas state only the configurations.
Neither sweep reads u.

### One round

After either sweep, the round runs exactly as in M18_4round (`ROUND_after_sweep`, for p ≥ 3 and a even):

| from tail | what runs | to tail |
|---|---|---|
| P at the left end: `(10)^(p+1) 0 (10)^(a/2+2) 0 u'` | bounce | `0 (10)^(p−2) 0 (10)^(a/2+2) 0 u'` at level pa_0 |
| `0 (10)^(p−2) …` | p − 2 alt steps (`Kd2_alt_loop`) | `0 0 (10)^(a/2+2) 0 u'` |
| `0 …` | one D1 cycle (`D1_cycle_all`) | `1 0 (10)^(a/2+2) 0 u'` = `(10)^(a/2+2) 1 0 0 u'` |
| `(10)^(a/2+2) 1 0 …` | a/2 + 2 Kd2 steps (`Kd2_loop`) | `1 0 0 u'` |

    Round_step (p, a) = Kd2_iter (a/2 + 2) (D1_cycle (Kd2_alt_iter (p − 2) pa_0))
    Ce_gen p a 0 (1 0 0 1 0 0 1 1 u)  →+  Ce_gen (Round_step (p, a)) 0 (1 0 0 1 0 1 0 u)     [Round_odd_step]
    Ce_gen p a 0 (1 0 0 1 0 1 0 u)    →+  Ce_gen (Round_step (p, a)) 0 (1 0 0 1 0 0 u)       [Round_even_step]

(both for p ≥ 5 and a ≥ 4 even). The round leaves `1 0 0` in front of the sweep's output, so the odd round's output
`1 0 1 0 u` becomes the even header, and the even round's output `1 0 0 u` becomes `1 0 0 1 0 0 u`: the odd header
again if u starts with `1 1`. An odd round followed by an even round is `Round_pair_step`; by induction on m,

    Ce_gen pa 0 (1 0 0 1 0 0 1^(2m) u)  →*  Ce_gen (Round_step^(2m) pa) 0 (1 0 0 1 0 0 u)                    [Round_pair_loop]

A round is p − 2 f_(ω+2) steps from the fixed start pa_0, one D1 cycle, and a/2 + 2 more f_(ω+2) steps: about
f_(ω+3) of the old level.

## 2. The run

| phase | what runs | result |
|---|---|---|
| opening | as in M16_B: `init_ce0` (21854 steps, to `Ce_gen 0 4 0 (1^230)`), then `start_boot` | pa_0 = (26, W_21(1)): `Ce_gen 26 W_21(1) 0 ((10)^10 0 1 0 0 1^228)` [`init_ce`] |
| round 1 | 9 Kd2 steps on (10)^9, as in M16_B | pa_R1 = `Kd2_iter 9 pa_0`, tail `1 0 0 1 0 0 1^228` [`Kd2_loop`] |
| rounds 2–229 | 114 odd/even pairs, with u the blank tape | pa_R229 = `Round_step^228 pa_R1`, tail `1 0 0 1 0 0` [`Round_pair_loop 114`] |
| halt | E, F, I, N, Q, R, N, then Q reads 0 | `c_end` pa_R229 [`HALT_step`, `run_to_end`, `halt`] |

The even rounds are rounds 3, 5, …, 229. The halting tape is 0^∞ (10)^p 1^(a+2) 1 1 0 1 1 1 1 [Q on 0] 0^∞ with
(p, a) = pa_R229, which holds p + a + 8 ones (`ones_c_end`, `score_exact`). The halting transition writes 1 on the
0 under the head, so σ = N + 1 = p + a + 9.

**Size** (`BB18_229round_fw3.v`, sections "Fast-Growing Hierarchy …" and "Domination …"). `ok_pa n (p, a)` says
n ≤ p − 5 and 4n + 6 ≤ a. The start satisfies ok_pa 9 pa_0 (`ok_pa_0`). Round 1 gives ok_pa f_(ω+3)(9)
(`Kd2_iter_dom`). Each later round maps ok_pa n to ok_pa f_(ω+3)(n) (`Round_step_dom`): the alt loop from pa_0 is
f_(ω+2)^(p−2)(9) ≥ n, the D1 cycle raises it, and then a/2 + 2 ≥ n Kd2 steps follow. By induction over the 228
later rounds (`Round_iter_dom`), f_(ω+3)^229(9) ≤ p − 5 (`halt_f_omega3_229`), so f_(ω+3)^229(9) < N
(`sigma_lower_bound`). As in M18_4round, every round has slack (a/2 + 2 is far more than n), but the file proves
only this bound.

## 3. Verification

[`verify_m18r229/`](verify_m18r229/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 40 s.
`BB18_229round_fw3.v` is Argon's file, unmodified. `probe.v` re-checks the transition table entry by entry against
the string above (36 checks generated from the string) and the blank start configuration. It prints the definitions
the statements use and confirms that `halt`, `score_exact` and `sigma_lower_bound` are closed under the global
context.

[`tools/m18r229_writeup_chk.py`](tools/m18r229_writeup_chk.py) simulates the machine string cell by cell, without
the Coq files (about 10 s). It checks:

- the opening reaches `Ce_gen 0 4 0 (1^230)` after 21854 steps, and in its first 10^7 steps reads none of N0, O1,
  P0, Q0, Q1, R0, R1 (so up to there the run is M16_B's); it reads N1, O0 and P1;
- `SWEEP_odd` and `SWEEP_even` on 49 instances each (p = 1..7, a = 0..12 even, random u): the claimed
  configurations after 4p + a + 22 and 4p + a + 18 steps, u never read; neither sweep reads Q0;
- `bounce_155` and the first part of `P0_bounce` (to `Ce_gen 22 8 1 (0 r)`, step 1627) on five tails r, and
  `CE_EVEN` on 45 small instances;
- the halt from `Ce_gen p a 0 (1 0 0 1 0 0)` on 16 instances: seven steps, then Q reads 0 in exactly `c_end p a`,
  with p + a + 8 ones;
- the engine pieces `D1_REL`, `C_REL_full` and `D2_STEP_full` on small instances: they reach the stated
  configurations, and read no slot outside A–M other than N1, O0 and P1;
- the tail bookkeeping as words: from `1 0 0 1 0 0 1^228`, the odd and even header rewrites alternate 114 times
  each and leave `1 0 0 1 0 0`, the halting header: 229 rounds.

The rest of the run is too large to simulate: a_0 = W_21(1) is already astronomically large.

## 4. Comparisons (an argument, not a Coq lemma)

The comparisons below are arguments on paper. No Coq lemma compares this machine with another entry: none of the
machines below has a proved upper bound.

- **M18_4round** (the previous BB(18) entry, and the BB(18) row of the wiki's Champions table as of 2026-11-04):
  proved f_(ω+3)^4(9) < σ. Since f_(ω+3)(x) > x, f_(ω+3)^229(9) > f_(ω+3)^4(9).
- **f_(ω+4)(9)**: f_(ω+4)(9) = f_(ω+3)^9(9) < f_(ω+3)^229(9). The machine is still f_(ω+3)-class in structure (a
  fixed number of f_(ω+3) rounds), but its proved bound is above f_(ω+4)(9).
- **M17_B** ([`../BB17/`](../BB17/)) and **BB18_fw3**: below f_(ω+3)^4(9) already (M18_4round write-up, section 4).
- **M19_fw4_A and M19_fw4** ([`../BB19/`](../BB19/)): proved f_(ω+4)(f_(ω+3)(9)) < σ and
  f_(ω+4)(f_(ω+2)(114)) < N. With Y = f_(ω+2)(114) > 229, f_(ω+4)(Y) = f_(ω+3)^Y(Y) > f_(ω+3)^229(9), so both 19-state
  bounds are higher. The wiki's BB(19) row (Jacobzheng, f_(ω+7)(f_(ω+7)(5))) is far above all of them.
- Not yet reviewed by the bbchallenge community.

## 5. Relation to other entries

- **M18_4round** (previous BB(18) entry): the same rows A–N and P. Its Q1 = `0LO` clears the header's last 1 and
  R reads one more cell, so the tail holds three headers (`1 0 0 1`, `1 0 0 0 0 1`, and the halting `1 0 0 0 1`)
  and the 1^227 is never read. Here Q passes 1s (Q1 = `1RR`) and R writes over 0s (R0 = `1RN`), so the reader runs
  on into the 1^228 and the reservoir becomes 114 header pairs.
- **M17_B** (BB(17)): the same rows A–P except O1; M17_B ends with 114 Kd1 steps on the 1^228 and one more D1
  cycle.
- **M16_B** (BB(16)): the same rows A–M; the opening and round 1 are M16_B's.

## Credit

Found and proved in Coq by Argon (a Google Gemini model run by the repository owner in Google's Antigravity),
2026-11-03: the machine and `BB18_229round_fw3.v` with `halt`, `score_exact` and `sigma_lower_bound`. This project
(the repository owner with Claude models (Anthropic) as agents) wrote the write-up, the probe and the literal
checker, did the packaging, and re-checked the proofs (from-scratch build, `Print Assumptions`, the probe).
