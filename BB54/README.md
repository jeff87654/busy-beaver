# BB(5, 4)

BB(5,4) champion **1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ**
(the machine in `../bb54.txt`): an **axiom-free Coq proof that the machine
halts**, together with the **exact value of its σ** and a machine-checked
analysis of the structure of the run.

This machine is the BB(5,4) champion of the Busy Beaver Challenge *up to the
renaming of the states A↔B and of the symbols 2↔3*; `tools/explore.py` checks
the equivalence exhaustively.  It is the machine the wiki's Champions page
lists for BB(5,4).

## The two runtime bounds

The Champions page listed, for BB(5,4), the **runtime** bound

    > f_ω² (10 ↑^4 10 ↑↑ 65533) .

That number is **Jacobzheng's original lower bound** — Jacobzheng, 2026, the
wiki marking it *"not independently verified"*.  It is the number that appears
in the question this development answers, and it is the **smaller** of the
two bounds below.

The bound that the structure of the machine itself gives — the one the wiki's
entry is being corrected to — is

    > f_ω² (2 ↑^4 2 ↑^3 4)   =   f_ω² (2X + 4)  ,

where `X = g_5(g_4(0))` is the descent parameter of the main regime.  The
identity `2 ↑^4 2 ↑^3 4 = 2X + 4` is **proved in Coq** (`X_inner` of
`BB54_bound.v`): the inner argument of the refined bound is a number *of the
machine itself* — it is exactly the number of twos that the first D/E phase
of the main regime has to erase — and not a generic tower.

The three numbers come out in the order

    f_ω² (10 ↑^4 10 ↑↑ 65533)   <   σ   <   f_ω² (2 ↑^4 2 ↑^3 4)  ,

so the inequality asked for, "σ > f_ω(f_ω(10 ↑^4 10 ↑↑ 65533))", **does
hold**: Jacobzheng's bound is below the σ of the machine, and the refined
bound is above it.  The comparison of the three is a hand calculation on the
closed forms; the inner tower comparison `10 ↑↑ 65533 < 2 ↑^3 4` on which it
rests is, however, **proved in Coq** (`BB54_tower.v`).  See
[The size of σ](#the-size-of-σ).

The write-up of the mathematics is in
[1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ.md](1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ.md);
the Coq development is in [verify/](verify/).

## What is proved

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
| `sigma_eq` | `BB54_score.v` | `sigma = knuth 4 2 3 + 4`, i.e. **σ = (2 ↑^3 4) + 4 = 2^65536 + 4** at that point of the run |
| `bb54_main` | `BB54_score.v` | all of the above in one statement |
| `D_phase_even`, `D_phase_odd` | `BB54_dphase.v` | the D/E phase for an **arbitrary** number of twos: an even number continues, an odd number halts the machine |
| `bb54_dchain` | `BB54_dphase.v` | `B(5,0,g_4(0)) [3 1] 0^inf -->* B(2X+1,1,0) [3 1]^3 0^inf` with `X = g_5(g_4(0))` |
| `level`, `level_gen` | `BB54_dphase.v` | a level of the main regime: `T` rounds (a B rule and an A3 sweep each) |
| `reaches_d1` | `BB54_halt.v` | `c0 -->* B(2X+1,1,0) [3 1]^3 0^inf` |
| `level0`, `level1` | `BB54_halt.v` | the two levels of the main regime |
| **`bb54_halt`** | **`BB54_halt.v`** | **the machine halts**: `c0 -->* E;; (3^(2M1) E> 3 (1 3)^(M0+X/2+1) 1 0^inf)`, the head being on a 3 in state E, where `E3 = 1RZ` |
| `sigma_final` | `BB54_halt.v` | the number of nonzero cells at halting: **σ = 2 M1 + 2 M0 + X + 5** |
| `bb54_halt_main` | `BB54_halt.v` | the run and its σ in one statement |
| `knuth_3_2_4` | `BB54_bound.v` | `2 ↑^3 4 = 2 ↑↑ 65536` — the shape of the third arrow |
| `knuth_4_2_3` | `BB54_bound.v` | `2 ↑^4 3 = 2 ↑^3 4` |
| `g4_zero_closed` | `BB54_bound.v` | `2 g_4(0) + 4 = 2 ↑^3 4` — the level-4 closed form |
| **`X_inner`** | **`BB54_bound.v`** | **`2 ↑^4 2 ↑^3 4 = 2X + 4`** — the inner argument of the refined runtime bound is the descent parameter of the machine |
| `target_is_jacobzheng` | `BB54_bound.v` | the wiki's entry is Jacobzheng's original bound: `target = f_ω²(10 ↑^4 10 ↑↑ 65533)` |
| **`target_refined_eq`** | **`BB54_bound.v`** | **the refined runtime bound is `f_ω²(2 ↑^4 2 ↑^3 4) = f_ω²(2X + 4)`** |
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

## The run

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

## The size of σ

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

So the wiki's original entry (Jacobzheng's bound) is *below* the σ of the
machine, and the bound derived from the machine is *above* it: the latter is
the accurate one, and it is the one the wiki's runtime entry is being
corrected to.

**This is a hand calculation on the closed forms, not a Coq proof.**  What
*is* proved in Coq is the identification with the machine and the direction
of the inner towers:

* `target = f_ω²(10 ↑^4 10 ↑↑ 65533)` (`target_is_jacobzheng`) — the wiki's
  entry is Jacobzheng's original bound;
* `2 ↑^4 2 ↑^3 4 = 2X + 4` (`X_inner`) — the inner argument of the refined
  bound is the descent parameter of the machine;
* `f_ω²(2 ↑^4 2 ↑^3 4) = f_ω²(2X + 4)` (`target_refined_eq`);
* `10 ↑↑ 65533 < 2 ↑^3 4` (`tower10_lt`, `tower10_lt_tower3`) — the
  inequality that decides the comparison of the two bounds, and whose
  direction an earlier version of this write-up had reversed.

## Build

    cd verify
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

Needs Coq 8.20.1 and a busycoq checkout (the `verify/` directory of it); the
whole build takes about 40 s.  See [verify/README.md](verify/README.md) for
details.

## Layout

    README.md                                       this file
    1LD3LB---2RA_...1RZ.md                          the mathematical write-up
    verify/                                         the Coq development
    tools/sim.py                                    a small Python simulator
    tools/explore.py                                the equivalence with the wiki champion
    tools/macro_d.py                                the D/E phase, step by step
    tools/macro_e.py                                the (k,n,m) parameters of the run
    tools/gen_start.py                              generator for verify/BB54_start.v

## Status

**The machine halts, and its σ is known exactly.**  `BB54.v`,
`Individual54.v`, `BB54_rules.v`, `BB54_start.v`, `BB54_run.v`,
`BB54_score.v`, `BB54_dphase.v`, `BB54_halt.v`, `BB54_bound.v`,
`BB54_tower.v` and `probe.v` all compile from scratch on Coq 8.20.1, and
`probe.v` reports that all 79 of the theorems it checks are *closed under
the global context* — that is, the proof uses no axioms at all.

What is *not* proved in Coq is the comparison of the three numbers above: the
argument in [The size of σ](#the-size-of-σ) is a hand calculation on the
closed forms.  The formalisation of that comparison would need a library of
inequalities between Knuth arrows, which is not part of this development.
