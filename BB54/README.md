# BB(5, 4)

## Current entry: 54-L (Argon)

```
1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE
```

Halts from the blank tape (B1 = `1RZ`). Machine-checked, axiom-free, for σ the number of nonzero cells after the
halting write:

    F^65536(65536) < σ                 (sigma_beats_f_omega1_65536: f_omega1 (2 ^ 16) < sigma)
    F(F(2 ↑^4 2 ↑^3 4)) < σ            (sigma_beats_official_bb54: f_omega2 (knuth 4 2 (knuth 3 2 4)) < sigma)

where **F(n) = 2 ↑^(n+1) (n + 3)** is `f_omega` of the files (the Knuth-arrow function of the previous entry's
`BB54_score.v`, not the fast-growing hierarchy's f_ω; it is at least as large, so on paper
f_(ω+1)(65536) < σ for the FGH). The exact σ is 2·M + K + 5 for (K, M) = `step_pair` iterated 2·g_4(0) + 5 times
from (0, 1) (not evaluated).

**Comparison with the previous entry (below), in Coq.** Jacobzheng's machine has an exact σ in Coq, and
[`verify_54l/BB54_J_upper.v`](verify_54l/BB54_J_upper.v) (written here, loading the published development) proves
the upper bound of the section [The size of σ](#the-size-of-σ) below, which was a hand calculation:
`sigma_final_upper : sigma_final <= f_omega2 (knuth 4 2 (knuth 3 2 4))`. With 54-L's `sigma_beats_official_bb54` this
gives `new_beats_jacobzheng : TM54.BB54_halt.sigma_final < Local.BB54_run.sigma`, both σ counted after the halting
write. Not yet reviewed by the bbchallenge community.

**The wiki.** The bbchallenge wiki's Champions page (read 2026-11-13) now lists for BB(5,4) a newer machine,
`1RB3LB1RD2RA_2LC3RB1LC2RA_3RB1LB3LC2RC_1LE2LE3LE1RZ_3RC2LE1LE3LE` by Big_numbers (Nov 2026), with the runtime bound
> f_ω^3(2 ↑^15 5), marked "not independently verified". That machine is not compared here: no upper bound for it is
known to us, so no claim is made against it.

54-L runs Kropitz's 3-state, 4-symbol engine (states A, C, E) with two more states (B, D) that turn the 3-stack of
the first descent into a reservoir of 2·g_4(0) + 5 twos on the right; each two then drives one level lift
(`D_step`: B(k+1, 0, m) 2 r → B(2m+1, 0, g_(2m)^(k+2)(0)) r), so the arrow level is lifted 2 ↑^3 4 + 1 times before
the machine halts in B reading 1.

- [`1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE.md`](1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE.md):
  the write-up.
- [`verify_54l/`](verify_54l/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `bb54_halts`, `reaches_final`,
  `final_halted`, `final_cells_count`, `final_cells_all_nonblank`, `sigma_beats_official_bb54`,
  `sigma_beats_f_omega1_65536`, `bb54_new_champion_main`, and the comparison `sigma_final_upper`,
  `new_beats_jacobzheng`. Built and probed in CI (job `bb54`, after `verify/`), which requires 11 closed
  `Print Assumptions` reports.

Found and proved by **Argon** (a Google Gemini model run by the repository owner), 2026-11-09 (54-L is a label used
here). Re-checked and packaged here, 2026-11-13.

## Previous entry: Jacobzheng's machine (2026-11-08 to 2026-11-13)

The BB(5,4) machine **1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ** (Jacobzheng, 2026; the machine the bbchallenge wiki's Champions page listed
for BB(5,4) when this entry was added).  The Coq development here, by MiniMax (contributed by loader3229, PR #48), proves two things, axiom-free:

* **the machine halts from the blank tape** (`bb54_halts : halts tm c0`, `BB54_halt.v`);
* **the exact value of its σ**, as a closed expression in Ligocki's `g` hierarchy (`bb54_halt_main`):

      σ = 2 M1 + 2 M0 + X + 5 ,   X = g_5(g_4(0)),  M0 = gchain (2X) 3 0,  M1 = gchain (2 M0) (X+2) 0 .

**No comparison of σ with the wiki's bound is proved in Coq.**  The Champions page lists for BB(5,4) the
runtime bound `> f_ω²(10 ↑^4 10 ↑↑ 65533)` (Jacobzheng, marked "not independently verified").
[The size of σ](#the-size-of-σ) below is a hand calculation on the closed forms which places σ between two
numbers:

    f_ω² (10 ↑^4 10 ↑↑ 65533)   <   σ   <   f_ω² (2 ↑^4 2 ↑^3 4)     (on paper, not in Coq).

The left inequality gives the wiki's bound on paper (the runtime is at least σ).  The right-hand number is an
*upper* bound for σ, not a new lower bound.  What the hand calculation rests on is partly in Coq: the inner
tower comparison `10 ↑↑ 65533 < 2 ↑^3 4` (`BB54_tower.v`) and the identity `2 ↑^4 2 ↑^3 4 = 2X + 4`
(`X_inner` of `BB54_bound.v`).

In this development `f_ω(n)` means `2 ↑^(n+1) (n+3)` (`f_omega` of `BB54_score.v`).  This is a Knuth-arrow
function, not the fast-growing hierarchy's f_ω.  It is at least as large as the FGH f_ω, so on paper a lower
bound written with it implies the same bound with the FGH f_ω.

The write-up of the mathematics is in
[1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ.md](1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ.md);
the Coq development is in [verify/](verify/).

### What is proved

| theorem | file | statement |
| --- | --- | --- |
| `start` | `BB54_start.v` | `c0 -->* Bcfg 2 1 0 0^inf` — the blank tape reaches the Ligocki configuration in 9 steps |
| `B_rule` | `BB54_rules.v` | `B(k+1,n,m) R -->* B(k+1, 0, g_k^n(m)) R` — Ligocki's Theorem 3, proved by double induction |
| `D_phase_raw` | `BB54_rules.v` | the BB(5,4)-specific D/E phase: `B(2,0,m) 0^inf -->* B(2m+1,1,0) [3 1] 0^inf` |
| `D_phase_halt` | `BB54_rules.v` | the D/E phase with an **odd** number of twos halts (`E3 = 1RZ`) |
| `D_phase_halt_1` | `BB54_rules.v` | the same for a single two |
| `macro_descent` | `BB54_rules.v` | one level down: `B(k,n+1,m,r) -->* B(k-1, 2m+2, 0) [3 1^n r]` |
| `B1_iter` | `BB54_rules.v` | the base case: `B(1,n,m,r) -->* B(1,0,m+n) r` |
| `a3_step` | `BB54_rules.v` | the A3 sweep: `B(k,0,m, 3 1^b r) -->* B(k+1,b,m) r` |
| `chain_step`, `chain` | `BB54_rules.v` | the long chain: `B(2,n,m) [3 r] -->* B(2,0, 2^n(m+2)-2) [3 r]` |
| `reaches_score` | `BB54_run.v` | `c0 -->* c_score`, where `c_score = B(5,0,g_4(0)) [3 1] 0^inf` |
| `sigma_eq` | `BB54_score.v` | `sigma = knuth 4 2 3 + 4`: an *intermediate* count, the nonzero cells of `c_score`, (2 ↑^3 4) + 4 = (2 ↑↑ 65536) + 4; not the σ of the machine (that is `sigma_final`) |
| `bb54_main` | `BB54_score.v` | `reaches_score` and `sigma_eq` in one statement (the intermediate configuration, not the halt) |
| `D_phase_even`, `D_phase_odd` | `BB54_dphase.v` | the D/E phase for an **arbitrary** number of twos: an even number continues, an odd number halts the machine |
| `bb54_dchain` | `BB54_dphase.v` | `B(5,0,g_4(0)) [3 1] 0^inf -->* B(2X+1,1,0) [3 1]^3 0^inf` with `X = g_5(g_4(0))` |
| `level`, `level_gen` | `BB54_dphase.v` | a level of the main regime: `T` rounds (a B rule and an A3 sweep each) |
| `reaches_d1` | `BB54_halt.v` | `c0 -->* B(2X+1,1,0) [3 1]^3 0^inf` |
| `level0`, `level1` | `BB54_halt.v` | the two levels of the main regime |
| **`bb54_halts`** | **`BB54_halt.v`** | **`halts tm c0` — the machine halts from the blank tape** (from `bb54_halt`, since `E3` is `None` in `tm`) |
| **`bb54_halt`** | **`BB54_halt.v`** | **the machine halts**: `c0 -->* E;; (3^(2M1) E> 3 (1 3)^(M0+X/2+1) 1 0^inf)`, the head being on a 3 in state E, where `E3 = 1RZ` |
| `sigma_final` | `BB54_halt.v` | the number of nonzero cells at halting: **σ = 2 M1 + 2 M0 + X + 5** |
| **`bb54_halt_main`** | **`BB54_halt.v`** | the run to the halting configuration and its σ in one statement (the headline) |
| `knuth_3_2_4` | `BB54_bound.v` | `2 ↑^3 4 = 2 ↑↑ 65536` — the shape of the third arrow |
| `knuth_4_2_3` | `BB54_bound.v` | `2 ↑^4 3 = 2 ↑^3 4` |
| `g4_zero_closed` | `BB54_bound.v` | `2 g_4(0) + 4 = 2 ↑^3 4` — the level-4 closed form |
| **`X_inner`** | **`BB54_bound.v`** | **`2 ↑^4 2 ↑^3 4 = 2X + 4`** — the inner argument of the refined runtime bound is the descent parameter of the machine |
| `target_is_jacobzheng` | `BB54_bound.v` | `target` (a definition) unfolds to `f_ω²(10 ↑^4 10 ↑↑ 65533)`, the wiki's number written with this `f_omega` |
| `target_refined_eq` | `BB54_bound.v` | `f_ω²(2 ↑^4 2 ↑^3 4) = f_ω²(2X + 4)` (the upper comparison number, rewritten) |
| `tower10_inv` | `BB54_tower.v` | the invariant of the tower comparison: `4 · (10 ↑↑ n) + 4 ≤ 2 ↑↑ (n+3)` |
| **`tower10_lt`** | **`BB54_tower.v`** | **`10 ↑↑ 65533 < 2 ↑↑ 65536`** — the inner tower of Jacobzheng's bound is *below* the inner tower of the refined one |
| **`tower10_lt_tower3`** | **`BB54_tower.v`** | **`10 ↑↑ 65533 < 2 ↑^3 4`** — the same, in the form in which the two bounds write it |

`knuth n a b` is Knuth's `a ↑^n b` with `a ↑^0 b = a·b` and `a ↑^(n+1) b = (a ↑^n b)^b 1`.

**No large number is ever evaluated.**  `g 4` unfolds to an exponentially
large term (`g 4 x` iterates `g 3` `2x+2` times, so normalising it also
normalises its argument), and `2 ↑^3 4` is beyond any arithmetic.  Both are
kept symbolic: `g40` is sealed behind a `sig` so that no tactic can evaluate
it, and `knuth 4 2 3` is only ever manipulated by rewriting.  See
[verify/coq_quirks.md](verify/coq_quirks.md) for the details — and for the
three further tricks that the halting proof needs (the big numbers are
*notations* rather than definitions, they are sealed with `Opaque` where they
occur inside a list, and every arithmetic step is a `rewrite`).

### The run

    0^inf A> 0^inf  -(9 steps)->      B(2, 1, 0)  0^inf
        ->  B(2, 0, 2)  0^inf                     (B_rule, level 1)
        ->  B(5, 1, 0)  [3 1] 0^inf               (the D/E phase, 14 steps)
        ->  B(5, 0, g_4(0))  [3 1] 0^inf          (B_rule, level 4)

and then the main regime, which has **two levels**:

    B(5, 0, g_4(0))  [3 1] 0^inf
        ->  B(6, 1, g_4(0))  0^inf                (the A3 sweep)
        ->  B(6, 0, X)  0^inf                    (B_rule, level 5)   X = g_5(g_4(0))
        ->  B(2X+1, 1, 0)  [3 1]^3 0^inf         (the D/E phase: 2X+4 twos, even)

    level 0:  3 rounds  ->  B(2 M0+1, 1, 0)  [3 1]^(X+2) 0^inf
        ->  the D/E phase sees 2M0+2X+4 twos, even, so the machine continues

    level 1:  X+2 rounds  ->  B(2M0+X+3, 0, M1)  0^inf
        ->  the D/E phase sees 2M0+X+3 twos, **odd** (X is even), so the
            machine arrives in state E on the first three of the block of
            threes -- and E3 = 1RZ halts it.

`M0` and `M1` are the numbers of threes at the two levels,
`M0 = gchain (2X) 3 0` and `M1 = gchain (2M0) (X+2) 0`, where
`gchain j T m` is the nested application of the `g`'s with the indices
`j, j+1, …, j+T-1`.

The final tape is

    0^inf  3^(2 M1)  E>  3  (1 3)^(M0 + X/2 + 1)  1  0^inf ,

so the number of nonzero cells at halting is

    σ = 2 M1 + 2 M0 + X + 5 .

### The size of σ

`g` is a tower of tetrations in disguise: `2 g_(k+1)(m) + 4 = 2 ↑^k (2m+4)`
(Ligocki's closed form, proved in `BB54_score.v` as `g_closed`).  Call the
number of arrows of a number of the form `2 ↑^k (·)` its **level**.  The
levels of the numbers of this run are then

| number | closed form | level |
| --- | --- | --- |
| `g_4(0)` | `2 ↑^3 4 / 2` | 3 |
| `X = g_5(g_4(0))` | `2 ↑^4 (2 ↑^3 4) / 2` | 4 |
| `M0 = g_(2X+3)(g_(2X+2)(g_(2X+1)(g_(2X) 0)))` | `2 ↑^(2X+2) (…)/2` | `2X+2` |
| `M1 = g_(2M0+X+1)(…)` | `2 ↑^(2M0+X) (…)/2` | `2M0+X` |
| `σ = 2 M1 + 2 M0 + X + 5` | `2 ↑^(2M0+X) (…)` | `2M0+X` |

so σ sits at level `2M0+X`, and that level is *itself* a number of level
`2X+2`, because `2 M0 = 2 ↑^(2X+2) (… ) - 4`.

The two bounds of the wiki, written the same way (`f_ω(n) = 2 ↑^(n+1)(n+3)`,
so `f_ω(n)` has level `n+1`):

| number | level | level of the level |
| --- | --- | --- |
| `f_ω²(10 ↑^4 10 ↑↑ 65533)` (Jacobzheng) | `f_ω(A)+1`, `A = 10 ↑^4 10 ↑↑ 65533` | `A+1` — level 4, argument `10 ↑↑ 65533` |
| `f_ω²(2 ↑^4 2 ↑^3 4)` (refined) | `f_ω(B)+1`, `B = 2 ↑^4 2 ↑^3 4 = 2X+4` | `B+1 = 2X+5` — level 4, argument `2 ↑^3 4` |
| `σ` | `2M0+X` | `2X+2` — level 4, argument `2 ↑^3 4` |

Three elementary facts about the towers do the comparison:

* `10 ↑↑ n < 2 ↑↑ (n+3)` for every `n ≥ 1`; in particular

      10 ↑↑ 65533  <  2 ↑↑ 65536  =  2 ↑^3 4 ,

  so the base-10 tower of the wiki's bound is *below* the base-2 tower of
  the refined bound, not above it.  **This inequality is proved in Coq**
  (`tower10_lt` and `tower10_lt_tower3` of `BB54_tower.v`, via the
  invariant `4 · (10 ↑↑ n) + 4 ≤ 2 ↑↑ (n+3)`);
* at the 4-arrow level a change of base from 2 to 10 costs at most two
  levels, `2 ↑^4 m < 10 ↑^4 m < 2 ↑^4 (m+2)`;
* a number of strictly larger level is larger, whatever its argument.

It follows that `A = 10 ↑^4 (10 ↑↑ 65533) < 2 ↑^4 (2 ↑^3 4) = B`, so that

    level of Jacobzheng's bound  =  A+1  <  2X+2  =  level of σ
                                      <  2X+5  =  level of the refined bound ,

and therefore

    f_ω² (10 ↑^4 10 ↑↑ 65533)   <   σ   <   f_ω² (2 ↑^4 2 ↑^3 4) .

So, on paper, the wiki's bound (Jacobzheng's) is *below* the σ of the
machine, and `f_ω²(2 ↑^4 2 ↑^3 4)` is *above* it, i.e. it is an upper bound
for σ.

**This is a hand calculation on the closed forms, not a Coq proof.**  What
*is* proved in Coq is the identification with the machine and the direction
of the inner towers:

* `target = f_ω²(10 ↑^4 10 ↑↑ 65533)` (`target_is_jacobzheng`, an unfolding:
  the wiki's number, written with this `f_omega`);
* `2 ↑^4 2 ↑^3 4 = 2X + 4` (`X_inner`) — the inner argument of the upper
  comparison number is the descent parameter of the machine;
* `f_ω²(2 ↑^4 2 ↑^3 4) = f_ω²(2X + 4)` (`target_refined_eq`);
* `10 ↑↑ 65533 < 2 ↑^3 4` (`tower10_lt`, `tower10_lt_tower3`) — the
  inequality that decides the comparison of the two bounds, and whose
  direction an earlier version of this write-up had reversed.

### Build

    cd verify
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

Needs Coq 8.20.1 and a busycoq checkout (the `verify/` directory of it); the
whole build takes about 40 s.  See [verify/README.md](verify/README.md) for
details.

### Layout

    README.md                                       this file
    1LD3LB---2RA_...1RZ.md                          the mathematical write-up
    verify/                                         the Coq development
    tools/sim.py                                    a small Python simulator
    tools/explore.py                                the equivalence with the wiki champion
    tools/macro_d.py                                the D/E phase, step by step
    tools/macro_e.py                                the (k,n,m) parameters of the run
    tools/gen_start.py                              generator for verify/BB54_start.v

### Status

**The machine halts, and its σ is known exactly.**  `BB54.v`,
`Individual54.v`, `BB54_rules.v`, `BB54_start.v`, `BB54_run.v`,
`BB54_score.v`, `BB54_dphase.v`, `BB54_halt.v`, `BB54_bound.v`,
`BB54_tower.v` and `probe.v` all compile from scratch on Coq 8.20.1, and
`probe.v` reports that all 80 of the theorems it checks are *closed under
the global context* — that is, the proof uses no axioms at all.

What is *not* proved in Coq is the comparison of the three numbers above: the
argument in [The size of σ](#the-size-of-σ) is a hand calculation on the
closed forms.  The formalisation of that comparison would need a library of
inequalities between Knuth arrows, which is not part of this development.
