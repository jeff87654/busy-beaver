# 3RD1LE2RA1LF_0LE2LE2RB2RD_1RF1RC2RB0LB_0RC0LD3RC2RA_1RC2LE1LG2RF_0LA0LD3LG1RZ_1LD2RA2LG0RB (BB(7,4))

Found by loader3229.  The blank-tape run halts; the Coq development in
[verify/](verify/) proves this without axioms, and proves the exact score

    sigma = 2 * mfin + 7 .

The score bound formalised here is

    f_(omega+3)(21) < sigma .

## Transition table

      0      1      2      3
A   3RD    1LE    2RA    1LF
B   0LE    2LE    2RB    2RD
C   1RF    1RC    2RB    0LB
D   0RC    0LD    3RC    2RA
E   1RC    2LE    1LG    2RF
F   0LA    0LD    3LG    1RZ
G   1LD    2RA    2LG    0RB

The only halting transition is `F3 = 1RZ`; `F2 = 3LG` is not a halt (this is
the difference from BB83).  `verify/probe.v` re-parses the machine string
inside Coq and checks all 28 entries of the table.

## Notation and the shared descent

As in BB34/BB73/BB83, busycoq left streams are listed from the head outwards, and

    Bcfg k n m r = 0^inf 1^(2m+1) 2^k B> 1^n r .

The BB34 recursion is

    g_0(m)     = m + 1
    g_(k+1)(m) = g_k^(2m+2)(0)

and the main rule is

    B(k+1, n, m) r  →  B(k+1, 0, g_k^n(m)) r .

The shared descent after rule 2 is

    B(k+2, 0, m) 0 r  →  B(k+1, 2m+2, 0) 0 r .

These are proved in `BB74_rules.v` as `B_rule` and `rule2`, exactly as in BB83.

## The BB74 tail rules

After 730 steps the blank run reaches

    B(2, 1, 0) 0^3 1^2 2^21 3 2 1 0^inf .

The first descent (`initial_desc`) gives `B(1,0,6) 0^3 1^2 2^21 3 2 1`.
The tail automaton then reads the markers after a leading 0:

1. `B(1,0,m) 0 0 r → B(1,0,round m) 0 r` (`rule3a` + `round_step`);
2. `B(1,0,m) 0 1 r → B(2,1,0) 0^(2m+3) r` (`rule3b`), followed by a new
   initial descent and a run through the new zero block (`epoch`);
3. `B(1,0,m) 0 2 r → B(2,1,0) 0^3 1^(2m+3) r` (the new `rule3c`), which
   after two rounds and `2m+3` epochs becomes `B(1,0,gamma m) 0 r`;
4. `B(1,0,m) 0 3 r` leads to `F` reading the 3, and `F3 = 1RZ` halts.

Here

    round m = desc (2m+2) (g_(2m+2)(0))
    next m  = round^(2m+2)(6)
    gamma m = next^(2m+3)(round^2 6) .

The parameter chain is

    m1  = round^2 6
    m2  = next m1,  m3 = next m2       (the two 1 markers)
    m4  = gamma m3, ..., m24 = gamma m23  (the twenty-one 2 markers)
    mfin = m24 .

`mfin` is sealed behind a `sig` so that Coq never evaluates it.

## Halting and sigma

`BB74_run.v` proves

    c0 -->* Bcfg 1 0 m24 (0 >> 3 >> 2 >> 1 >> const 0)
       -->* (1 >> [1]^^(2*mfin+4) 0^inf) F> (3 >> 2 >> 1 >> const 0) .

State F reads the final 3 and halts.  The halting write turns that 3 into a 1,
so the final tape contains

    (2*mfin+4) + 1 + 1 + 1 = 2*mfin + 7

nonzero cells.  Hence `sigma = 2*mfin + 7`, proved via `final_cells_count` and
`final_cells_all_nonblank`.

## Score bound

`BB74_score.v` keeps the BB73/BB83 Knuth machinery:

    2 g_(k+1)(m) + 4 = 2 ↑^k (2m+4)
    2 round(x) + 4   = aw 0 (2x+2) (2 ↑^(2x+1) 4)
    round(x) + 2     = aw 1 (2x+1) (2 ↑^(2x+1) 4)

and proves `round x > f_omega x` for `x >= 1`, where
`f_omega x = 2 ↑^(x+1) (x+3)`.  Define

    f_omega1 n = f_omega^n n        = f_(omega+1)(n)
    f_omega2 n = f_omega1^n n       = f_(omega+2)(n)
    f_omega3 n = f_omega2^n n       = f_(omega+3)(n) .

Write `achain j = next^j(m1)`, so `achain 2 = m3` and
`gamma(achain j) = achain (2 * achain j + 3)`.  The formalised chain is:

* `21 < achain 2 = m3`;
* `f_omega2` is strictly increasing on positive arguments, so
  `f_omega2^21(21) < f_omega2^21(m3)`;
* iterating `f_omega1` at an achain point is absorbed by the next achain
  entry, hence `f_omega2(achain j) < gamma(achain j)` and, by induction,
  `f_omega2^21(m3) < gamma^21(m3) = m24`;
* therefore `f_omega3 21 < m24 < sigma`.

All these comparisons are symbolic; no Ackermann-level natural number is ever
normalised.

## Machine-checked statements

| theorem | file | statement |
| --- | --- | --- |
| `bb74_halts` | `BB74_run.v` | `halts tm c0` |
| `reaches_final` | `BB74_run.v` | `c0 -->* c_final` |
| `final_halted` | `BB74_run.v` | `halted tm c_final` (`F3 = 1RZ`) |
| `fomega3_21_lt_sigma` | `BB74_score.v` | `f_omega3 21 < sigma` |
| `bb74_main` | `BB74_score.v` | all of the above, with `sigma = 2*mfin+7` |

The clean build reports the main statements closed under the global context
and no axioms.
