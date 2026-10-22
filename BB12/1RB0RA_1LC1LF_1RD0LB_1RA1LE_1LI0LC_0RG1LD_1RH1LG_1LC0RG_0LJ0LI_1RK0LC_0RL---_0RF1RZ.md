# T12a: a 12-state machine at level f_(ω+1)²

    1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RK0LC_0RL---_0RF1RZ

> **Note (2026-10-22).** "The BB(8) record" on this page is `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_1LC0RH_1RG1LF`
> (σ = 12·(2↑^37 3) + 59), the BB(8) entry of this repository at the time of writing. Since 2026-10-18 the BB(8)
> entry is M8 ([`../BB8/README.md`](../BB8/README.md)); nothing on this page depends on that change.

Below we call this machine **T12a**. It halts from the blank tape, and Coq proves that its score is at least
(f_(ω+1)(f_(ω+1)(JJ − 2)) − 11)/6, where JJ = (3T − 13)/7 ≈ 0.43·T and T = 2↑^37 3 is the value computed by the BB(8)
record. T12a is the 10-state machine n1 ([`../BB10/`](../BB10/)) with two more states. It runs n1's whole computation,
rebuilds a countdown from n1's final values, and runs n1's period loop a second time. So it applies f_(ω+1) twice,
where n1 applies it once. Written 2026-10-11.

|   | 0   | 1   |                                                                   |
|---|-----|-----|-------------------------------------------------------------------|
| A | 1RB | 0RA |                                                                   |
| B | 1LC | 1LF |                                                                   |
| C | 1RD | 0LB |                                                                   |
| D | 1RA | 1LE |                                                                   |
| E | 1LI | 0LC |                                                                   |
| F | 0RG | 1LD |                                                                   |
| G | 1RH | 1LG |                                                                   |
| H | 1LC | 0RG |                                                                   |
| I | 0LJ | 0LI |                                                                   |
| J | 1RK | 0LC | J0 was n1's halting transition                                    |
| K | 0RL | --- | new; K1 is never read                                             |
| L | 0RF | 1RZ | new; L1 is the halt                                               |

**Where it comes from.** States A–J are n1. n1 halts when J reads 0. T12a sends that transition to two new states
K and L. K0 leads to L, L0 leads back into F (a state of the base machine), and L1 is the new halt. K1 is never read. The
standard string writes it as `---`, so in the strict sense T12a is a 12-state machine with one unused transition.

**Main facts.** T, JJ and F(x) = 2↑^x 4 are as in the n1 write-up. "ones" is the number of 1s on the tape when L
reads 1. The halting transition writes a 1 on a cell that already holds 1, so the standard score is σ = ones.

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms). |
| Lower bound | Machine-checked: F^(2J)(w) ≤ 6·ones + 11, where w ≥ F^(2JJ+1)(34) is n1's final depth and F(w) ≤ 7J + 9 (section 3.1). |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+1)(f_(ω+1)(JJ − 2)) ≤ 6·ones + 11. |
| n1 | **Beaten**, machine-checked against n1's own Coq-proved exact score. |
| Exact score | Not computed. No upper bound is proved. |

---

## 1. How it works

### 1.1 Notation

We use the notation of the n1 write-up ([`../BB10/`](../BB10/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC.md), section 1.1).

- D(t) = (10)^t 1 is the token t.
- `[t_1, …, t_k | A]` is a configuration with the tokens left to right and the accumulator A next to the head.
- 1 is a **zero** and `1^n` is a run of n zeros.
- A **clearing** at depth j maps the value v = (A + 8)/3 to 2↑^j v.
- `Per(k, m, n, A) = [2^k, 5, 1^m, 0, 0, 2, 1^n | A]` is a period start: debris k, counter m, depth n,
  accumulator A.
- `X + [ … ]` means the far-left pattern X followed directly by the configuration. The far-left patterns are:
  - FarE(k) = D2^k followed by n1's fixed 44 cells, written by n1's last unpack E;
  - FarR(k) = D2^k D1 D8 followed by two blank cells, written by T12a's restart.

### 1.2 Round 1: n1's run

States A–J are n1. Until J reads 0, T12a is n1, so it follows n1's run exactly:
- the BB(8) record's computation, which yields T;
- the countdown of 6T − 19 zeros;
- JJ = (3T − 13)/7 periods, each an f_ω-sized step on the depth;
- n1's endgame.

It reaches n1's halting configuration

    FarE(k) + [0, 1^w | f]          k = 4·JJ − 3,   w ≥ F^(2JJ+1)(34)

where n1 halts, with J reading 0. Coq re-proves n1's rules and run for the 12-state machine (`reach_end`). The depth w is n1's
final zero block W, and f is its final accumulator.

### 1.3 The restart

In T12a, J0 does not halt. It goes to K, then L, then back into F, and a series of special events follows
(`W_R1END`, `W_E0`–`W_E8`, `W_E10`–`W_E12`, with clearings in between). Their net effect is Coq's `restart` lemma:

    FarE(7 + k) + [0, 1^(w) | f]   →   FarR(k) + [3, p, 2, 5, 1^(14J+3), 0, 0, 2, 1^n | a]
                                     =  FarR(k) + [3, p] + Per(1, 14J + 3, n, a)

with n ≥ w, the period invariant (n ≥ 3, A ≡ 1 mod 3, v ≥ F(n)), and **F(w) ≤ 7J + 9**.

- **It works in place.** The restart rewrites only the 44-cell pattern and 7 of the D2 debris tokens. The rest of
  the debris, D2^k, is untouched. Unlike n1's start (event H), nothing is written at a new far-left position.
- **The new counter comes from the old accumulator.** The restart clears f, then a chain of eleven values, each
  derived from the previous one.
  - The first eight clearings are at depths between w − 1 and w + 4. The fifth, at depth w + 3, outputs 4 + 3x,
    and x becomes the counter 2x − 7 = 14J + 3.
  - The last three clearings are at depths of size F(w), and the last one gives round 2's accumulator a.
  - A token p, the output of one of the deep clearings, is left in front of the new period start. Nothing reads it
    again.
  - Coq keeps only the weak bounds F(w) ≤ 7J + 9 and n ≥ w. In fact J and n are much larger.
- **The counter lands in a halting class.** Coq proves x ≡ 5 (mod 7) (via `arrow_mod7`), so the counter has the
  form 14J + 3. It falls by 14 per period, so round 2 ends with exactly 3 counter zeros left. In n1 the counter
  ended at 7, which leads to event E.

### 1.4 Round 2: n1's period loop again

From `Per(1, 14J+3, n, a)`, T12a runs n1's period loop (section 3 of the n1 write-up) J times. Coq's `PERIOD` and
`PERIODS` hold for any far-left context, so the same lemmas apply with FarR(k) + [3, p] on the left:

    FarR(k) + [3, p] + Per(1, 14J + 3, n, a)   →   FarR(k) + [3, p] + Per(1 + 4J, 3, n', a')
                                                   with n' ≥ F^(2J)(n) ≥ F^(2J)(w)

(`reach_round2_end`). Each period again takes the depth from n to at least F(F(n)). Round 2 makes J periods, and J
is at least (F(w) − 9)/7 with w itself at f_(ω+1) size. That is where the second f_(ω+1) comes from.

### 1.5 The end of round 2 and the halt

The round ends with 3 counter zeros instead of 7. A different event, E20, then fires, and the depth list is
converted and eaten (`END_PER`):

    Per(4 + K, 3, n, A)
      E20      →  S20(K) + [2, 2, 0, A, 1^3, 0, 1^n | 6]
      CONVERT  →  S20(K) + [2, 2, 0, A − 7, 2, 0, (3, 2, 0)^n, 1^4 | A24]
      EAT      →  six blocks (3, 2, 0) per loop round, right to left; one junk unit per round
      CONT     →  L reads 1: the halt

- **S20(K)** is D2^K followed by 23 fixed cells.
- **CONVERT** turns each zero of the depth list into a block (3, 2, 0). The accumulator becomes
  A24 = U_3³(4), three units cleared at depth 3 from a reset. Coq proves A24 ≡ 4 (mod 9) (`A24_form`: clearing
  outputs from 4 are towers of 2, which are 1 mod 3).
- **EAT** runs one of six loops, chosen by the number of blocks n mod 6 (`EAT0`–`EAT5`; Coq requires n ≥ 6). Each round of a loop eats six blocks and
  leaves one 78-cell junk unit on the far side.
- **The continuation** depends only on the remainder class:
  - classes 2, 3 (`CONT23`): the token A24 + 3 = 43 + 9y is turned into y junk units (`W_F23`, `W_F24`), one
    clearing, then the halt (`WH_HALT1`);
  - classes 0, 1 (`CONT01`): CONVERT turns three more zeros into blocks, `W_SM3` follows, and then the class-2/3
    path above;
  - classes 4, 5 (`CONT45`): `W_G1`, a clearing, `W_G2`, `W_G3`, another clearing, then the halt (`WH_HALT2`).

All six classes halt, so the proof never needs to know the real depth class. The halt is reached with L reading 1
(L1 undefined, `1RZ` in the string).

### 1.6 What the new states cost

- **The engine.** States A–J do all the clearing, parking and unpacking, in both rounds.
- **K and L.** These two states and the rewired J0 are only read in the restart (section 1.3) and the round-2 end
  (section 1.5). Their job is to rebuild a countdown from the current values and to halt at the end. This comes
  from simulation; the Coq proof does not state it.
- **Why T12a halts after round 2.** The restart lands the new counter in the class that ends with 3 zeros, not
  the class of round 1 that ends with 7. That 3-zero class leads to the halt.

---

## 2. The run

| | configuration | how | proved in Coq |
|---|---|---|---|
| 0 | blank tape, state A | | |
| 1 | `FarE(k) + [0, 1^w \| f]`, k = 4·JJ − 3, w ≥ F^(2JJ+1)(34) | n1's whole run (round 1) | `reach_end` (n1's rules, re-proved for 12 states) |
| 2 | `FarR(k−7) + [3, p] + Per(1, 14J+3, n, a)`, n ≥ w, F(w) ≤ 7J + 9 | the restart | `restart` |
| 3 | `FarR(k−7) + [3, p] + Per(1+4J, 3, n', a')`, n' ≥ F^(2J)(w) | J periods (round 2) | `PERIODS`, `reach_round2_end` |
| 4 | L reads 1 | E20, CONVERT, EAT, CONT, then `WH_HALT1` or `WH_HALT2` | `END_PER`, `END_EAT`, `halt` |

The number of steps has not been computed. It is far larger than the score.

---

## 3. The score

### 3.1 What Coq proves

From [`verify/multifile/BB12_T12a_bound.v`](verify/multifile/BB12_T12a_bound.v):

- `sigma_lower_bound`: the halting tape holds N ones, and for some J and w,

      F^(2JJ+1)(34) ≤ w,      F(w) ≤ 7J + 9,      F^(2J)(w) ≤ 6N + 11.

  The last inequality comes from the EAT phase. The depth list n' ≥ F^(2J)(w) is eaten six blocks at a time, and
  each round leaves one junk unit on the tape. So N ≥ (n' − 11)/6.
- `score_ge_exact`: F(F(Wf)) ≤ 6N + 11, with Wf = n1's exact final depth in closed form (the recursion `step` /
  `stepn` of the n1 write-up, sections 3 and 4.4).
- `beats_n1`: N > n1's exact standard score (`BB10_n1_exact.score_value + 1`). Coq proves that the two files'
  definitions of arrow, `step`, `stepn` and JJ agree.

From [`verify/multifile/BB12_T12a_fgh.v`](verify/multifile/BB12_T12a_fgh.v), with the standard fast-growing
hierarchy of [`BB10_n1_fgh.v`](verify/multifile/BB10_n1_fgh.v) (f_0(x) = x + 1, f_(k+1)(x) = f_k applied x times to
x, f_ω(x) = f_x(x), f_(ω+1)(x) = f_ω applied x times to x):

- `fgh_lower2`: f_(ω+1)(f_(ω+1)(JJ − 2)) ≤ 6N + 11.

  The proof:
  1. n1's `lower_from` gives w ≥ f_(ω+1)(JJ − 2).
  2. F(w) ≥ 7w + 9 gives J ≥ w.
  3. n1's `fo_iter_le` (f_ω^j(m) ≤ F^(2j)(m)) gives
     f_(ω+1)(w) = f_ω^w(w) ≤ f_ω^J(w) ≤ F^(2J)(w) ≤ 6N + 11.
  4. f_(ω+1) is increasing (`f_omega1_mono`), so step 1 gives
     f_(ω+1)(f_(ω+1)(JJ − 2)) ≤ f_(ω+1)(w).

### 3.2 How large

On paper, the Coq bounds give roughly ones ≳ f_(ω+1)(f_ω(f_(ω+1)(JJ))). Round 1 gives w ≈ f_(ω+1)(JJ). The restart
turns w into a countdown of J periods. Coq proves J ≥ (F(w) − 9)/7, where F(w) ≈ f_ω(w). From the restart lemma,
J is about 2↑^(w+4)(F(w+3)): above F(w), and roughly below f_ω(f_ω(w)). Each period of round 2
applies F twice, which is at least f_ω (Coq: f_ω(x) ≤ F(F(x))). Without an upper bound, we only claim the lower bound of section 3.1.

### 3.3 Comparison with the published champions

The bounds are from the bbchallenge wiki "Champions" page, as of 2026-10-11. On that page, a row is blank when a
smaller machine already beats that size.

| n | champion | published lower bound | compared with T12a | status |
|---|---|---|---|---|
| 10 | n1 (Ketchersid 2026) | f_(ω+1)(2↑^36 3) | T12a is larger | **Coq** (`beats_n1`, against n1's Coq-proved exact score) |
| 11–13 | blank (n1) | | T12a is larger than n1 | follows from the row above |
| 14 | Jacobzheng 2026 | f_(ω+1)(f_ω⁴(f_7(3))) | T12a's lower bound is larger | on paper |
| 15 | Jacobzheng 2026 | f_(ω+1)²(10^10^57) | T12a's lower bound is larger | on paper |
| 16 | Jacobzheng 2026 | f_(ω+1)³(f_ω²(f_6²(3))) | larger than anything claimed here | no claim |

The paper comparisons use `fgh_lower2` and monotonicity. Both 10^10^57 and f_7(3) are below 2↑^9 9: n1's `fgh_le`
gives f_7(3) ≤ 2↑^9 9, and 10^10^57 < 2↑↑6. So both are far below JJ − 2 ≈ 0.43·T, where T = 2↑^36 4. For n = 14, f_(ω+1)(JJ − 2) = f_ω^(JJ−2)(JJ − 2) ≥ f_ω⁴(f_7(3)). For n = 15,
f_(ω+1)(f_(ω+1)(JJ − 2)) > f_(ω+1)(f_(ω+1)(10^10^57)). The factor 6 and the +11 are negligible at this size. The
comparisons assume the wiki uses the same standard definitions.

As in the n1 write-up, the BB(14) and BB(15) entries have published lower bounds only. So these comparisons show
that T12a's proved lower bound exceeds their published lower bounds, not that T12a outscores those machines.
Because BB is increasing, T12a would raise the known lower bounds for BB(12) through BB(15), if accepted.

---

## 4. Verification

### 4.1 What Coq proves

The development is in [`verify/multifile/`](verify/multifile/). It uses Coq 8.20.1 on top of
[busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`). See [`verify/README.md`](verify/README.md).

| statement | Coq name | file |
|---|---|---|
| T12a halts from the blank tape | `halt` | `BB12_T12a.v` |
| round 1 = n1's run; the restart; round 2; the round-2 end; all six EAT classes | `reach_end`, `restart`, `PERIODS`, `reach_round2_end`, `WE_E20`, `CONVERT`, `EAT0`–`EAT5`, `CONT01`, `CONT23`, `CONT45`, `END_EAT`, `END_PER` | `BB12_T12a.v` |
| the lower bound of section 3.1 | `sigma_lower_bound`, `score_ge_exact` | `BB12_T12a_bound.v` |
| T12a beats n1 | `beats_n1` | `BB12_T12a_bound.v` (with the `BB10_n1*.v` files) |
| f_(ω+1)(f_(ω+1)(JJ − 2)) ≤ 6·ones + 11 | `fgh_lower2` | `BB12_T12a_fgh.v` (with `BB10_n1_fgh.v`) |

`BB12_T12a.v` is a 2.6 MB file. Most of its 14,268 lines are lemmas generated from event specifications, each
validated by literal simulation before it was proved. The halting proof imports nothing from the n1 files: it
re-proves n1's rules for the 12-state machine. The n1 files (byte-identical to
[`../BB10/verify/multifile/`](../BB10/verify/multifile/)) are used only by `beats_n1` and `fgh_lower2`, but
`BB12_T12a_bound.v` Requires them, so they are compiled first.

`compile_clean.sh` rebuilds all 16 files from scratch and runs `probe.v`. Most of the time goes to
`BB12_T12a.v`: 9989 s (2.8 h) in the recorded build, at Idle priority on a shared laptop; the whole build took
3.1 h. The probe does three things:

- it checks all 24 entries of the transition table against the machine string, by conversion;
- it prints the definitions the statements use (`arrow`, `F`, `iter`, `T_def`, `JJ`, `ones`, `step`, `stepn`,
  `Wf`, `fgh`, `f_omega1`, …);
- it runs `Print Assumptions` on the five main theorems. All five report "Closed under the global context".

The logs of that from-scratch build (2026-10-11, busycoq compiled fresh from commit `bd2e36f`) are
`compile_clean.log` and `probe.log`; `sha256.txt` has the hashes of the sources.

### 4.2 Not machine-checked

- The comparisons with the BB(14) and BB(15) champions (section 3.3). They are on paper.
- The size estimates of section 3.2.
- Which transitions each phase reads (section 1.6). This comes from simulation.

### 4.3 Checks before the proof

Before the Coq proof, the round-2 end was checked by independent simulators: a literal simulator, and a symbolic
follower that keeps the huge values as exact tower residues and orders them by size. They agreed that T12a halts
in L1 for every residue class of the depth, and the Coq proof then covered all six classes. There is no
separate literal checker in this folder; every rule of section 1 is a Coq lemma.

---

## 5. Discovery and credit

- **Found** on 2026-10-09 by a computer search over 12-state extensions of n1. The search replaced n1's halting
  transition J0 with gadgets of up to two new states and kept those whose round-1 end rebuilds a countdown in
  place from the accumulator.
- **Checked** by independent simulation (section 4.3), then **proved** in Coq on 2026-10-10.
- **Built on** n1 ([`../BB10/`](../BB10/)), the BB(8) record (Ketchersid 2026, [`../BB8/`](../BB8/)) and the BB(7)
  champion (Kropitz 2025, analysis by Ligocki).
