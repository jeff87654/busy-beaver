# A 14-state machine at level f_(ω+2)³

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LN1RF_1LJ0RA_1RA0LH_1LG1LH_1RK0LM_1RZ0LE_0LE0RJ_1LH1LM_0LH0LL_0LG1LN

Below we call this machine **M14**. It halts from the blank tape, and Coq proves that its score σ satisfies

    σ > f_(ω+2)(f_(ω+2)(f_(ω+2)(15)))

with the standard fast-growing hierarchy. The tape holds an Ackermann-type evaluator with a level stack, an
accumulator and two counters. A map Kc on (level, accumulator) evaluates W at the current level; two Kc steps make an f_ω-sized step. The inner counter iterates Kc,
which gives an f_(ω+1)-sized step. The outer counter iterates that, which gives an f_(ω+2)-sized round. When a round
ends, the accumulator is reloaded into the outer counter. A parity argument shows that the machine halts at the end
of the third round. M14 and both Coq proofs were found and written by Argon, a Google Gemini model. Argon started
from the evaluator of Jacobzheng's 14-state f_(ω+1) champion and compressed it (section 5). Written 2026-10-14.

|   | 0   | 1   |                                                       |
|---|-----|-----|-------------------------------------------------------|
| A | 1RB | 1RA |                                                       |
| B | 1RI | 1RC |                                                       |
| C | 0LD | 1LG |                                                       |
| D | 0RE | 1LD |                                                       |
| E | 1LN | 1RF |                                                       |
| F | 1LJ | 0RA |                                                       |
| G | 1RA | 0LH |                                                       |
| H | 1LG | 1LH |                                                       |
| I | 1RK | 0LM |                                                       |
| J | 1RZ | 0LE | J0 is the halt                                        |
| K | 0LE | 0RJ |                                                       |
| L | 1LH | 1LM |                                                       |
| M | 0LH | 0LL |                                                       |
| N | 0LG | 1LN |                                                       |

The string is not in visit-order normal form. Renaming the states in order of first visit from the blank tape
(same directions) gives the equivalent form
`1RB1RA_1RC1RJ_1RD0LM_0LE0RG_1LH1RF_1LG0RA_1RZ0LE_0LI1LH_1RA0LL_0LK1LI_0RE1LK_1LI1LL_0LL0LN_1LL1LM`. This write-up
and the Coq files use the string above.

**Main facts.** "ones" is the number of 1s on the tape when J reads 0. The halting transition J0 = `1RZ` writes a 1
on a cell that holds 0, so the standard score is σ = ones + 1.

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms). |
| Exact score | Machine-checked as a recursion: ones = p₃ + a₃ + 2, so σ = p₃ + a₃ + 3, where (p₃, a₃) is defined by the maps Kc, Kd and D_reload (sections 1.3, 1.4 and 2). Not evaluated. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+2)(f_(ω+2)(f_(ω+2)(15))) < σ, and the stronger f_(ω+2)(f_(ω+2)(f_(ω+1)^15(f_ω(21)))) < σ. |
| Published champions | The BB(12) entry T12a and the published lower bounds of the bbchallenge wiki for BB(14)–BB(16) are smaller, **on paper** (section 3.3). No comparison is made with the f_(ω+2)-class BB(17) and BB(18) champions. |
| Upper bound | None proved. |

---

## 1. How it works

### 1.1 Notation

- `0^∞ X A> Y` means: the tape is blank to the left of the word X, then X, then the word Y, then blank. The
  head is on the first cell of Y, in state A.
- `0^∞ X <H Y` means the same, but the head is on the **last** cell of X, in state H. (This is busycoq's
  `l <{{H}} r`.) If X is empty, the head is on a blank cell.
- `(10)^j` is j copies of the word `10`. `1^b` is b ones.
- z, y, r stand for arbitrary tape contents to the right. They are never read by the rule in question.

The configuration families of the Coq file [`BB14_M14.v`](verify/multifile/BB14_M14.v):

| family | tape | role |
|---|---|---|
| `Ci(p, a, c, d)` | `0^∞ (10)^p 1^(a+1) I> 1^c 0 1^d 0^∞` | the main configuration: level p, accumulator a, inner counter c, outer counter d |
| `Ca(j, b, z)` | `0^∞ (10)^j 1^b A> 0 z` | evaluator, moving right |
| `Ch(j, b, z)` | `0^∞ (10)^j <H 1^(b+1) 0 z` | evaluator, about to read the level stack |
| `Ch0(j, c, d)` | `0^∞ (10)^j <H 0 0 1^c 0 1^d 0^∞` | evaluator, at the start of a reload |
| `blk(a, z)` | the word `1^(a+1) 0` followed by z | a count of a, to the right of the head |
| `c_end(p, a)` | `0^∞ (10)^p 1^(a+2) 0 J> 0^∞` | the halting configuration |

The pairs `(10)^p` at the left end form the **level stack**. Its height p is the index of the function the
evaluator computes. The block `1^(a+1)` is the **accumulator**. The two unary blocks to the right of the head are
the **inner counter** c and the **outer counter** d.

### 1.2 The evaluator: W

Coq defines

    W(0, b) = b + 3,        W(j+1, b) = W(j, ·)^(b+1) (2)        (b+1 applications of W(j, ·), starting from 2).

So W(1, b) = 3b + 5, W(2, b) = 4.5·3^(b+1) − 2.5, W(2, 2) = 119, W(3, 0) = 119. W(j, ·) grows like f_j. The basic rules
(state A sweeps right, H sweeps left; Coq names):

    CA_SH    Ca(j, b, 1 0 z)    →  Ca(j+1, b, z)                  a pair 10 to the right is pushed onto the stack
    CA_CH    Ca(j, b, 1 1 y)    →  Ch(j, b, 1 y)                  one unit of a count is taken, H goes left
    CH_0     Ch(0, b, z)        →  Ca(0, b+3, z)                  level 0: add 3
    CH_S     Ch(j+1, b, z)      →  Ca(j, 2, blk(b+1, z))          pop a pair; the block becomes a count of b+1,
                                                                    and a new block of size 2 starts
    CA_EXIT  Ca(j, b, 0 z)      →  0^∞ (10)^j 1^(b+2) I> z         leave the evaluator

From these, Coq proves by induction on j (`CH_CA` together with `BLK_iter_aux`):

    CH_CA    Ch(j, b, z)            →  Ca(j, W(j, b), z)
    BLK      Ca(j, b, blk(a, z))    →  Ca(j+1, W(j, ·)^a (b), z)

This is the usual tape evaluation of an Ackermann-type function. At level j+1 (rule CH_S), the top pair of the
stack is popped and the block is turned into a count of b+1 to the right. Each unit of the count (CA_CH) runs the
evaluator at level j on the new block. When the count is used up, `blk(0, z)` is `1 0 z`, and CA_SH pushes the pair
back.

### 1.3 The step map Kc

When the inner counter is nonzero, I reads its first 1. States M and L halve the accumulator, which becomes pairs
`10` to the right of the stack (Coq's `I_EVEN`, `I_ODD`). The evaluator then computes W at level p − 1. CA_SH
pushes the new pairs onto the stack and CA_EXIT returns to I. Coq's `CI_EVEN` and `CI_ODD`:

    Ci(p+1, 2k,   c+1, d)  →  Ci(p + k,   W(p, 1) + 1, c, d)
    Ci(p+1, 2k+1, c+1, d)  →  Ci(p + k+1, W(p, 0) + 1, c, d)

Together they give `Kc_step`, for p ≥ 1:

    Ci(p, a, c+1, d)  →  Ci(Kc(p, a), c, d),      Kc(p, a) = (p − 1 + ⌈a/2⌉,  W(p − 1, 1 − (a mod 2)) + 1).

So the old accumulator a becomes about a/2 new levels, and the new accumulator is W at the old level. Since
W(j, b) ≡ b + 1 (mod 2) (`W_par`), Kc flips the parity of the accumulator (`Kc_props`). Applying Kc c times empties
the inner counter (`Kc_loop`):

    Ci(p, a, c, d)  →  Ci(Kc^c(p, a), 0, d).

### 1.4 The outer counter, the reload and the halt

When the inner counter is empty, I reads the separator 0 (I0 = `1RK`). K and J then look at the outer counter:

    C_REL      Ci(p+1, a, 0, d+2)  →  Ci(p, 3, a+3, d)       the accumulator becomes the inner counter
    D_REL      Ci(p+2, a, 0, 0)    →  Ci(p, 3, 2, a+2)       the accumulator becomes the outer counter
    HALT_step  Ci(p, a, 0, 1)      →  c_end(p, a)            J reads 0: halt

After C_REL comes the c-loop, so the outer counter falls by 2 per **Kd step** (`Kd_step_all`):

    Ci(p, a, 0, d+2)  →  Ci(Kd(p, a), 0, d),       Kd(p, a) = Kc^(a+3)(p − 1, 3).

After D_REL come two Kc steps (`D_reload_all`):

    Ci(p, a, 0, 0)  →  Ci(D_reload(p, a), 0, a+2),       D_reload(p, a) = Kc²(p − 2, 3).

**Why it halts after three rounds.** A Kd step keeps the parity of the accumulator: it applies Kc a+3 times to an
accumulator of 3. D_reload always produces an odd accumulator: two Kc steps from 3. The outer counter after a
reload is a + 2, where a is the accumulator before the reload. So a round that starts with an even counter ends at
d = 0 and reloads, and a round that starts with an odd counter ends at d = 1 and halts. Coq tracks this parity
(`run_round_even`, `run_round_odd`):

- Round 1 starts with a = 6 and d = 32. It ends at d = 0 with a even.
- Round 2 starts with d = a₁ + 2 (even) and an odd accumulator. It ends at d = 0 with a odd.
- Round 3 starts with d = a₂ + 2 (odd). It ends at d = 1, and the machine halts.

### 1.5 What the states do

From simulation (the Coq proof does not state it):

- **A–H** do the evaluator: shifts, the level recursion, pushing pairs (rules of section 1.2).
- **I** dispatches on the inner counter: I1 starts a Kc step, I0 goes to the outer counter.
- **M, L** halve the accumulator at the start of a Kc step.
- **K, J** dispatch on the outer counter: K0 (d = 0) starts D_REL, J1 (d ≥ 2) starts C_REL, J0 (d = 1) is the halt.
- **N, E** move the accumulator into the inner counter (C_REL) or into the outer counter (D_REL).

### 1.6 Why this reaches f_(ω+2)³

These bounds are proved in [`BB14_M14_bound.v`](verify/multifile/BB14_M14_bound.v). In Coq's notation, "ok(n) for
(p, a)" means n ≤ p − 4 and n ≤ a/2.

1. **Levels.** For m ≥ 0 and every b, W(m+3, b) ≥ 2·f_ω(m+1) + 3 (`W_omega_bound`). The general comparison is
   2^(j+1)·f_(j+1)(n) ≤ W(j+1, z) whenever 2^(j+1)·n ≤ z (`W_bound_all`).
2. **Two Kc steps give one f_ω.** For p ≥ 4 and a ≥ 3, the level after two Kc steps is at least
   f_ω(p − 3) + 3 (`Kc_dom2`). The first step makes the accumulator f_ω-sized. The second step turns half of it into
   levels. So 2k Kc steps give f_ω^k (`Kc_dom_even`).
3. **A Kd step gives one f_(ω+1).** If n ≥ 1 and ok(n) holds for (p, a), then ok(f_(ω+1)(n)) holds for Kd(p, a)
   (`Kd_step_dom`). The step makes a + 3 Kc steps, which is at least n applications of f_ω, starting at level
   at least n.
4. **A round gives one f_(ω+2).** D_reload keeps ok(n) (`D_reload_dom`). The round then makes a/2 + 1 ≥ n Kd
   steps, so ok(f_(ω+2)(n)) holds at its end (`round_dom`).
5. **Round 1** is shorter. It has 16 Kd steps. The first one gives ok(f_ω(21)) (`Kd_step_first`): Kc takes
   (2, 3) to (3, 6), then to (5, 39), then to a pair of level 24. The other 15 steps give ok(f_(ω+1)^15(f_ω(21)))
   (`pa1_dom_strong`). Since f_ω(21) ≥ 15, this is at least ok(f_(ω+2)(15)) (`pa1_dom`).
6. **Rounds 2 and 3** each apply step 4 once. So ok(f_(ω+2)(f_(ω+2)(f_(ω+1)^15(f_ω(21))))) holds at the end of
   round 3 (`pa3_dom_strong`). If ok(n) holds for (p, a), then n < p + a + 2 + 1 (`ok_pa_score_lt`), and
   p₃ + a₃ + 2 is the ones count.

---

## 2. The run

| | configuration | how | proved in Coq |
|---|---|---|---|
| 0 | blank tape, state A | | |
| 1 | `Ca(1, 1, blk(2, 0^∞))`, step 26 | 26 single steps | `init_26` |
| 2 | `Ci(2, 30, 0, 0)`, step 578 | BLK at level 1: W(1, W(1, 1)) = 29, then CA_EXIT | `init_578` |
| 3 | `Ci(3, 6, 0, 32)`, step 801 | D_REL to `Ci(0, 3, 2, 32)`, 35 single steps to `Ci(2, 3, 1, 32)`, CI_ODD | `init_801` |
| 4 | `Ci(p₁, a₁, 0, 0)`, (p₁, a₁) = Kd^16(3, 6), a₁ even | round 1: 16 Kd steps | `run_pa1` |
| 5 | `Ci(p₂, a₂, 0, 0)`, (p₂, a₂) = Kd^(a₁/2+1)(D_reload(p₁, a₁)), a₂ odd | round 2 | `run_pa2` |
| 6 | `Ci(p₃, a₃, 0, 1)`, (p₃, a₃) = Kd^(a₂/2+1)(D_reload(p₂, a₂)) | round 3; d = a₂ + 2 is odd | `run_pa3` |
| 7 | `c_end(p₃, a₃)`: J reads 0, halt | HALT_step | `halt` |

In Coq, (p₁, a₁), (p₂, a₂), (p₃, a₃) are `pa1`, `pa2`, `pa3`. Already the first Kd step, Kd(3, 6) = Kc⁹(2, 3), is
out of reach of a simulator. Its third Kc step gives the accumulator W(4, 0) + 1, and W(4, 0) = W(2, W(2, 119)) is
about 10^(3.9·10^57). The number of steps has not been computed. It is far larger than the score.

---

## 3. The score

### 3.1 What Coq proves

From [`verify/multifile/BB14_M14_bound.v`](verify/multifile/BB14_M14_bound.v). "ones c N" means that the halting
configuration c holds N ones. The standard score is σ = N + 1, since the halting transition writes a 1 on a 0.

- `score_exact`: the halting configuration holds exactly p₃ + a₃ + 2 ones (the tape `(10)^p₃ 1^(a₃+2)`). So
  σ = p₃ + a₃ + 3, with (p₃, a₃) given by the recursion of section 2. This is exact, but nobody has evaluated it.
- `sigma_lower_bound`: f_(ω+2)(f_(ω+2)(f_(ω+2)(15))) < N + 1 = σ.
- `sigma_lower_bound_strong`: f_(ω+2)(f_(ω+2)(f_(ω+1)^15(f_ω(21)))) < N + 1 = σ.

The hierarchy is defined in the same file: f_0(n) = n + 1, f_(k+1)(n) = f_k^n(n), f_ω(n) = f_n(n),
f_(ω+1)(n) = f_ω^n(n), f_(ω+2)(n) = f_(ω+1)^n(n). These are the standard definitions.

### 3.2 How large

Only the lower bounds of section 3.1 are claimed. On paper, a Kd step from (p, a) applies f_ω about a/2 times.
The accumulator a was left by the last Kc step, so it is f_ω-sized in the level at which that step ran (Coq's
`Kc_dom1`), and in practice much larger than p. So one Kd step lies between f_(ω+1)(p) and roughly
f_(ω+1)(f_ω(p)). Each round applies f_(ω+2), or a little more, to the argument left by the round before. So the
strong bound has the right shape: three f_(ω+2)-sized rounds, the first one truncated to 16 Kd steps. The small
arguments (15, 21) are not sharp. No upper bound is proved.

Argon's original heading comment in [`BB14_M14.v`](verify/multifile/BB14_M14.v) said f_(ω+2)³(16). The published
copy states the proved bound, with 15 (see [`verify/README.md`](verify/README.md), Provenance).

### 3.3 Comparison with the published champions

The bounds are from the bbchallenge wiki "Champions" page, as of 2026-10-11.

| n | champion | published lower bound | compared with M14 | status |
|---|---|---|---|---|
| 12 | T12a ([`../BB12/`](../BB12/)) | f_(ω+1)(f_(ω+1)(JJ − 2)) ≤ 6N + 11 (Coq) | M14's lower bound is larger than T12a's score | on paper (T12a has no proved upper bound) |
| 13 | M13 ([`../BB13/`](../BB13/)) | f_(ω+2)(f_ω(20)) | M14's lower bound is larger than M13's lower bound | on paper |
| 14 | Jacobzheng 2026 | f_(ω+1)(f_ω⁴(f_7(3))) | M14's lower bound is larger | on paper |
| 15 | Jacobzheng 2026 | f_(ω+1)²(10^10^57) | M14's lower bound is larger | on paper |
| 16 | Jacobzheng 2026 | f_(ω+1)³(f_ω²(f_6²(3))) | M14's lower bound is larger | on paper |
| 17, 18 | f_(ω+2)-class champions | | **not compared** | no claim |

All three wiki bounds are below f_(ω+2)(15), which is smaller than σ. Everything below uses only monotonicity,
f_k(x) ≤ f_x(x) for x ≥ k, and f_3(n) > 2↑↑n for n ≥ 2:

- **n = 14.** f_7(3) ≤ f_ω(7). So f_ω⁴(f_7(3)) ≤ f_ω⁵(7) ≤ f_(ω+1)(7), and the wiki bound is at most
  f_(ω+1)²(7) < f_(ω+1)^15(15) = f_(ω+2)(15).
- **n = 15.** 10^10^57 < 2↑↑6 < f_3(6) ≤ f_ω(6). So the wiki bound is below f_(ω+1)³(6) < f_(ω+2)(15).
- **n = 16.** f_6(f_6(3)) ≤ f_ω(f_ω(6)). So f_ω²(f_6²(3)) ≤ f_ω⁴(6) ≤ f_(ω+1)(6), and the wiki bound is at most
  f_(ω+1)⁴(6) < f_(ω+2)(15).

**T12a** ([`../BB12/`](../BB12/)) has a Coq-proved lower bound only: f_(ω+1)(f_(ω+1)(JJ − 2)) ≤ 6N + 11, where
JJ < T = 2↑^37 3 < f_ω(40). It runs n1's computation and then n1's period loop a second time. So M14's proved lower
bound exceeds T12a's: f_(ω+1)²(JJ − 2) ≤ f_(ω+1)³(40) < f_(ω+2)(40) < f_(ω+2)(f_(ω+2)(15)). On paper (T12a
write-up, section 3.2) T12a's score is roughly f_(ω+1)(f_ω(f_(ω+1)(JJ))), which is below f_(ω+1)⁴(40) < f_(ω+2)(40).
So M14 beats T12a, but only by this paper estimate, not against a proved value.

**M13** ([`../BB13/`](../BB13/), in the same release) is a 13-state machine whose Coq proof uses the same kind of
recursion (W, Kc, Kd, D_reload): one Kd step, then a single f_(ω+2) round, then the halt. Its proved bound, f_(ω+2)(f_ω(20)), is
below f_(ω+2)(f_(ω+2)(15)).

**BB(17), BB(18).** The published champions for 17 and 18 states are f_(ω+2)-class machines. We have not compared
their exact values with M14 and make no claim either way.

M14 is unrelated to n1 and T12a ([`../BB10/`](../BB10/), [`../BB12/`](../BB12/)). It does not contain them and does
not use the BB(8) record's value. It is derived from the BB(14) champion in the table, Jacobzheng's f_(ω+1)
machine: it shares that machine's evaluator and 20 of its 28 transitions (section 5.1).

As with the earlier entries, the BB(14)–BB(16) entries have published lower bounds only. So these comparisons show
that M14's proved lower bound exceeds their published lower bounds, not that M14 outscores those machines. Because
BB is increasing, M14 would raise the known lower bounds for BB(14) through BB(16), if accepted. The comparisons
assume that the wiki uses the same standard definitions of the hierarchy.

---

## 4. Verification

### 4.1 What Coq proves

The development is in [`verify/multifile/`](verify/multifile/). It uses Coq 8.20.1 on top of
[busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`). `BB142.v` and `Individual142.v` instantiate
busycoq for 14 states and 2 symbols. The state named L shadows busycoq's direction L, so the table writes directions
as `TM.L` and `TM.R`.

| statement | Coq name | file |
|---|---|---|
| M14 halts from the blank tape | `halt` | `BB14_M14.v` |
| the rules of section 1 | `CA_SH`, `CA_EXIT`, `CA_CH`, `CH_0`, `CH_S`, `CH_CA`, `BLK_iter_aux`, `CH0_CI`, `C_REL`, `D_REL`, `CI_EVEN`, `CI_ODD`, `Kc_step`, `Kc_loop`, `Kd_step_all`, `Kd_loop`, `D_reload_all`, `HALT_step` | `BB14_M14.v` |
| the start-up and the three rounds | `init_801`, `run_pa1`, `run_pa2`, `run_pa3` | `BB14_M14.v` |
| exact ones count p₃ + a₃ + 2 | `score_exact` | `BB14_M14_bound.v` |
| f_(ω+2)³(15) < σ | `sigma_lower_bound` | `BB14_M14_bound.v` |
| f_(ω+2)²(f_(ω+1)^15(f_ω(21))) < σ | `sigma_lower_bound_strong` | `BB14_M14_bound.v` |

The two files are short (626 and 610 lines). `compile_clean.sh` rebuilds the four `.v` files and runs `probe.v`;
the recorded build (`compile_clean.log`) took 28 s for the four files. See [`verify/README.md`](verify/README.md). `probe.v` checks all 28 entries of the transition table against the machine string, by conversion; these lines
were generated from the string, not from the Coq file. It also prints the definitions used in the statements
(`iter`, `f`, `f_omega`, `f_omega1`, `f_omega2`, `ones`, …) and runs `Print Assumptions` on the four main theorems.
All four report "Closed under the global context" (re-run here on 2026-10-14).

### 4.2 Not machine-checked

- σ = ones + 1. In Coq the halting transition J0 is `None`, and `ones` counts the 1s of the halted configuration.
  The extra 1 written by J0 = `1RZ` is the standard convention.
- The step numbers 578 and 801 of section 2. Coq proves that those configurations are reached; the step counts come
  from the simulator of section 4.3. (The 26 of `init_26` is `do 26 step` in Coq.)
- The comparisons of section 3.3, including the one with T12a. They are on paper.
- The size estimates of section 3.2.
- Which transitions each phase reads (section 1.5). This comes from simulation.
- The account of the search in section 5.1. It is taken from Argon's own notes. Several details in those notes do
  not match the verified machine.
- Argon's notes also list a different 14-state string as "M14":
  `1LB1LA_1RC0LA_1RD1RC_1RE1LF_1RF0LJ_1RG1RH_0LI0LM_1LF0LI_1LK0LC_1RZ1RJ_0LJ1RL_1LN1LK_0RE1RM_0RG1LN`. That is
  not the machine verified here. Its visit-order normal form differs from M14's, with or without mirroring. Its
  status is unknown.

### 4.3 Independent literal check

[`tools/m14_writeup_chk.py`](tools/m14_writeup_chk.py) is a cell-by-cell simulator written for this write-up,
separately from the Coq file. It builds each configuration family of section 1.1 on concrete values, with random
words for z, y and r. It then runs the machine until the predicted configuration appears exactly: same state,
same head position, same tape. It checks:

- the start-up: `Ca(1, 1, blk(2, 0^∞))` at step 26, `Ci(2, 30, 0, 0)` at step 578, `Ci(3, 6, 0, 32)` at step 801;
- CA_SH, CA_EXIT, CA_CH, CH_0, CH_S, CH0_CI, C_REL and D_REL on small grids of parameters;
- CH_CA against W for j ≤ 2 and for W(3, 0) = 119, and BLK for j ≤ 2;
- Kc_step for p ≤ 3, both parities of a, and several values of c and d; two-step Kc_loop chains;
- D_reload for p = 3 (giving (3, 9)) and p = 4 (giving (5, 39)), for a = 3, …, 11;
- HALT_step, that J0 is the only undefined transition, and that c_end(p, a) holds p + a + 2 ones;
- the visit-order form of section 1: renaming the states by first visit gives exactly that string, and the two
  machines run in lockstep for 10^6 steps (same tape and head, renamed state), through the start-up events at
  steps 26, 578 and 801.

It prints one PASS or FAIL line per rule and exits nonzero on a failure. Result (2026-10-14): all 18 lines PASS
(677 checks). A Kd step cannot be run literally, even for the smallest arguments, because Kd(2, 3) passes through
W(6, 1). The check covers its parts, C_REL and the Kc steps.

---

## 5. Discovery and credit

### 5.1 How it was found

This account is taken from Argon's own notes on the search, written on 2026-10-14 after the proofs. Only the
machine string and the Coq files are verified. We summarise the notes in four steps and then say where they do not
match the verified machine.

1. **The starting point.** The base was Jacobzheng's 14-state BB(14) champion,
   `0LH0LL_1RI1RC_0LD1LG_0RE1LD_---1RF_---0RM_1RM0LH_1LG1LH_0LN0RJ_1RZ0LK_0LK1LL_1LG1LA_1RB1RM_0LG1LN`.
   - It reaches f_(ω+1) and has an inner counter c, but no outer counter.
   - Two of its transitions, E0 and F0, are never used.
   - Its evaluator is one-sided: the level stack and the accumulator `(10)^p 1^(a+1)` grow only to the left, and
     the counter to the right of the head is left alone.
   - Argon chose this evaluator over the one in Jacobzheng's 17-state champion. According to the notes, that one
     puts the pairs to the right of the accumulator and needs extra states to shift them.
2. **Pipelining the f_(ω+1) layer.** In the champion, a c step uses two states (J and K) to decrement c and to put
   a seed digit at the right end of the accumulator. Then the pair rewriter halves the accumulator.
   - Argon sent I1 directly into the pair rewriter and set L0 = 1LH. The halving then ends by forming the seed block
     at the left end of the accumulator, next to the level stack.
   - The evaluator computes W at level p − 1 on that seed before the new pairs are pushed. So one c step turns the
     old accumulator into new levels and computes the new accumulator at the old level. This is Kc (section 1.3).
   - Two Kc steps still give one f_ω step, and J and K became free.
3. **The reloads.** The free states, together with the unused E0 and F0, had to implement C_REL, D_REL and the halt
   (section 1.4).
   - A backtracking search that asked for separate left-walking states for the two reloads found nothing.
   - Argon then judged each candidate only by the tape at the first moment the evaluator was re-entered. Once the
     evaluator is re-entered with the right counters on the tape, its existing rules do the rest. This search found
     the reload mechanism.
4. **Parity and the start-up.** Halting comes from the parity alternation of section 1.4. A final search over the
   remaining free transitions found the start-up from the blank tape, which reaches `Ci(2, 30, 0, 0)` at step 578
   and `Ci(3, 6, 0, 32)` at step 801 (section 2).

The search code for M14 was not preserved. The notes cite a program that no longer exists.

**What M14 shares with the champion.** Rename the champion's states A and M as M and A, and keep the other names.
- 20 of M14's 28 transitions are then identical to the champion's: all of A, B, C, D, G, H, M and N, plus E1, F1,
  J0 (the halt, `1RZ`) and L1.
- Two transitions fill slots that the champion never used: E0 = 1LN and F0 = 1LJ.
- Six transitions are changed: I0, I1, J1, K0, K1 and L0.
  - I1 = 0LM (the champion's I1 is 0RJ) and L0 = 1LH are the pipelining of step 2.
  - Simulation shows that I0, J1, K0 and K1, together with E0 and F0, do the outer-counter dispatch and the reloads.
- The start states differ: M14 starts in A, which is the champion's M.

We did not search for a renaming with more shared transitions.

**Where the notes do not match.** Several details in the notes (in Argon's own state names) do not match the
verified machine:
- an engine in which E and F are merged (G0 = 1LE, E1 = 0RM);
- a reload gadget with K0 = 0LJ, K1 = 1RF, F0 = 1RZ, F1 = 0LN, J0 = 0RI and J1 = 1LJ;
- a start-up with D0 = 0RG and E0 = 0LI.

The verified machine keeps the champion's E–F pair (E1 = 1RF, F1 = 0RA, G0 = 1RA) and has D0 = 0RE and E0 = 1LN. No
renaming of it has a transition 1L into a state whose 1-transition is 0R into the right-sweeping evaluator state, so
the merged engine of the notes is not M14's. The notes' summary table also gives a different string (section 4.2).
The step counts 578 and 801 and the lemma names `init_578` and `init_801` in the notes do match the Coq file. We do
not know whether the mismatched details describe an earlier candidate or are errors in the notes.

### 5.2 Credit and checks

- **Found and proved** by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity on
  2026-10-13. Argon wrote both Coq files, `BB14_M14.v` and `BB14_M14_bound.v`.
- **Built on** Jacobzheng's 14-state BB(14) champion (section 5.1).
- **Re-checked** independently here on 2026-10-13 and 2026-10-14:
  - a fresh compile with check.py (PASS);
  - [`verify/multifile/probe.v`](verify/multifile/probe.v), which checks the transition table entry by entry
    against the machine string, prints the definitions used, and runs `Print Assumptions` on the four main theorems
    (all closed, no axioms).

  This write-up and the literal checker of section 4.3 were written afterwards, from the Coq statements.
