# 2RD1LE2RA_0LE2LE2RB_1RF1RC2RB_0RC0LG1LD_1RC2LE1LG_1RG0LA1RZ_1LD2RA2LG (BB(7,3))

Found by loader3229 on 2026-11-17.
A 7-state, 3-symbol machine whose blank-tape run is a
`B(k,n,m)`-style Ackermann descent, followed by a 12-round tail automaton that
iterates the descent at ever larger levels.  The Coq development in
[verify/](verify/) proves (axiom-free) that it halts, with

    f_(omega+1)(11) < sigma .

The transition table is

      0      1      2
A   2RD    1LE    2RA
B   0LE    2LE    2RB
C   1RF    1RC    2RB
D   0RC    0LG    1LD
E   1RC    2LE    1LG
F   1RG    0LA    1RZ
G   1LD    2RA    2LG

The only halting transition is **F2 = 1RZ**; `verify/probe.v` re-parses the
machine string inside Coq and checks all 21 entries of `tm`.

## Notation

As in BB34/BB35, busycoq left streams are listed from the head outwards, and
`Bcfg k n m r` denotes

    0^inf  1^(2m+1)  2^k  B>  1^n  r .

`r` is the tail to the right of the `1^n` block; the marker that drives the
tail automaton is the first symbol of `r`.  A write `X → Y` below means zero
or more transitions (Coq's `-->*`).

The recursion from BB34 is

    g_0(m)     = m + 1
    g_(k+1)(m) = g_k^(2m+2)(0)

and the main rule (`BB73_rules.v`, `B_rule`) is

    B(k+1, n, m) r  →  B(k+1, 0, g_k^n(m)) r .

## The four macro rules (`BB73_rules.v`)

1. `B_rule`: `B(k+1,n,m) r → B(k+1,0,g_k^n(m)) r`, proved by the same double
   induction as BB34, from the sweeps `E_left_1s`, `G_left_2s`, `D_left_2s`,
   `A_right_2s`, `B_right_2s`, `C_right_1s` and the loops `EGA`, `EGAA`.

2. `rule2` (the BB35-style extra rule):

       B(k+2, 0, m) 0 r  →  B(k+1, 2m+2, 0) 0 r .

3. `rule3`:

       B(1, 0, m) 0 1 r  →  B(2m+3, 1, 0) 0 r .

4. `halt_from_B`:

       B(1, 0, m) 0 2 r  →*  (1 1^(2m+3) 0^inf) F> 2 r ,

   after which F reads the 2 and halts.

## The run

`BB73_start.v` proves the blank-tape run for 255 steps in 10-step chunks:

    0^inf A> 0^inf  -(255)->  B(1, 1, 0) 0 1^12 2 0^inf .

Then:

* `B_rule` with k=0, n=1 gives `B(1,0,1) 0 1^12 2`; set `m_0 = 1`.
* For each of the twelve 1s in the tail:

      B(1,0,m) 0 1 tail
        -(rule3)->        B(2m+3,1,0) 0 tail
        -(B_rule)->       B(2m+3,0,g_(2m+2)(0)) 0 tail
        -(rule2/B_rule)-> B(1,0,R(m)) 0 tail,

  where the descent consists of `2m+2` applications of rule 2 and uses
  `g_(2m+2), g_(2m+1), ..., g_1`.  In Coq:

      round m := desc (2m+2) (g (2m+2) 0)
      mfin    := round^12(1)   (sealed behind a sig).

* The tail is now `0 2`, so `halt_from_B` reaches the halting configuration

      1 1^(2 mfin + 3) 0^inf F> 2 0^inf .

The halting write turns the 2 into a 1, so the final tape contains
`(2*mfin+4) + 1 = 2*mfin+5` nonzero cells: `sigma = 2*mfin + 5`
(`BB73_run.v`, `final_cells`, `cells_count`).

## The score bound (`BB73_score.v`)

The Knuth-notation closed form of the `g` hierarchy is

    2 g_(k+1)(m) + 4 = 2 ↑^k (2m+4),

and for the `desc` recursion,

    2 desc(n,m) + 4 = 2 ↑^0 (2 ↑^1 (... (2 ↑^(n-1) (2m+4)) ...)).

Writing `aw j n x` for that nested expression, one round satisfies

    2*round(x) + 4 = aw 0 (2x+2) (2 ↑^(2x+1) 4)
                   = 2 * aw 1 (2x+1) (2 ↑^(2x+1) 4).

The innermost level of the right-hand side is `2 ↑^(2x+2) 4`.  Two standard
Knuth-inequalities (both machine-checked) imply

    2 ↑^(2x+2) 4 > 4 * f_omega(x),    x >= 1,

where `f_omega(x) = 2 ↑^(x+1) (x+3)`.  Hence `round(x) > f_omega(x)` for
`x >= 1`.  Also `round(1) > 11`, and `f_omega` is strictly increasing, so

    round^12(1) > f_omega^11(11) = f_(omega+1)(11).

Since `sigma = 2*mfin+5 > mfin`, the theorem `fomega1_lt_sigma` follows.

This uses the Knuth-arrow normal form `f_omega(n) = 2 ↑^(n+1) (n+3)`, which
is an upper bound for the usual fast-growing-hierarchy value `F_n(n)`; the
certified inequality is therefore at least as strong as
`F_(omega+1)(11) < sigma`.

## Machine-checked statements

| theorem | file | statement |
| --- | --- | --- |
| `bb73_halts` | `BB73_run.v` | `halts tm c0` |
| `reaches_final` | `BB73_run.v` | `c0 -->* c_final` |
| `final_halted` | `BB73_run.v` | `halted tm c_final` (`F2 = 1RZ`) |
| `fomega1_lt_sigma` | `BB73_score.v` | `f_omega1 11 < sigma` |
| `bb73_main` | `BB73_score.v` | all of the above, with `sigma = 2*mfin+5` |

No large number is ever evaluated: `mfin` is sealed behind a `sig`, `round`
and `f_omega` are made opaque before the iteration proof, and every Knuth
expression is handled symbolically.
