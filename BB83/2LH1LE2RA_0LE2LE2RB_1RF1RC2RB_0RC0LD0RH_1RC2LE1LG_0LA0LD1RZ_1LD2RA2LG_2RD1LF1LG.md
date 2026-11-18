# 2LH1LE2RA_0LE2LE2RB_1RF1RC2RB_0RC0LD0RH_1RC2LE1LG_0LA0LD1RZ_1LD2RA2LG_2RD1LF1LG (BB(8,3))

Found by loader3229 as an 8-state refinement of the BB(7,3) champion.  The
blank-tape run halts; the Coq development in [verify/](verify/) proves this
without axioms, and proves the exact score

    sigma = 2 * mfin + 7 .

The score bound formalised here is

    f_(omega+1)^3 ( f_omega^3(14) ) < sigma .

## Transition table

      0      1      2
A   2LH    1LE    2RA
B   0LE    2LE    2RB
C   1RF    1RC    2RB
D   0RC    0LD    0RH
E   1RC    2LE    1LG
F   0LA    0LD    1RZ
G   1LD    2RA    2LG
H   2RD    1LF    1LG

The halting transitions are `D2 = 0RH` and `F2 = 1RZ`; the blank run reaches
the latter.  `verify/probe.v` re-parses the machine string inside Coq and checks
all 24 entries of the table.

## Notation and the shared descent

As in BB34/BB73, busycoq left streams are listed from the head outwards, and

    Bcfg k n m r = 0^inf 1^(2m+1) 2^k B> 1^n r .

The BB34 recursion is

    g_0(m)     = m + 1
    g_(k+1)(m) = g_k^(2m+2)(0)

and the main rule is

    B(k+1, n, m) r  →  B(k+1, 0, g_k^n(m)) r .

The shared descent after rule 2 is

    B(k+2, 0, m) 0 r  →  B(k+1, 2m+2, 0) 0 r .

These are proved in `BB83_rules.v` as `B_rule` and `rule2`, exactly as in BB73.

## The BB83 tail rules

After 152 steps the blank run reaches

    B(2, 1, 0) 0^4 1^4 2 1 2 0^inf .

The first descent (`initial_desc`) gives `B(1,0,6) 0^4 1^4 2 1 2`.  The tail
automaton then reads the markers after a leading 0:

1. `B(1,0,m) 0 0 r → B(1,0,round m) 0 r` (`rule3a` + `round_step`);
2. `B(1,0,m) 0 1 r → B(2,1,0) 0^(2m+3) r` (`rule3b`), followed by a new
   initial descent and a run through the new zero block (`epoch`);
3. `B(1,0,m) 0 2 r` halts (`halt_from_B`).

Here

    round m = desc (2m+2) (g_(2m+2)(0))
    next m  = round^(2m+2)(6) .

The parameters are

    m1 = round^3(6),  m2 = next m1,  m3 = next m2,
    m4 = next m3,     m5 = next m4,  mfin = m5 .

They correspond to the initial zero block, then the four `1` reset markers in
`0^4 1^4 2 1 2`.  `mfin` is sealed behind a `sig` so that Coq never evaluates
it.

## Halting and sigma

`BB83_run.v` proves

    c0 -->* Bcfg 1 0 m5 (0 >> 2 >> 1 >> 2 >> const 0)
       -->* (1 >> [1]^^(2*mfin+4) 0^inf) F> (2 >> 1 >> 2 >> const 0) .

State F reads the final 2 and halts.  The halting write turns that 2 into a 1,
so the final tape contains

    (2*mfin+4) + 1 + 1 + 1 = 2*mfin + 7

nonzero cells.  Hence `sigma = 2*mfin + 7`, proved via `final_cells_count` and
`final_cells_all_nonblank`.

## Score bound

`BB83_score.v` keeps the BB73 Knuth machinery:

    2 g_(k+1)(m) + 4 = 2 ↑^k (2m+4)
    2 round(x) + 4   = aw 0 (2x+2) (2 ↑^(2x+1) 4)
    round(x) + 2     = aw 1 (2x+1) (2 ↑^(2x+1) 4)

and proves `round x > f_omega x` for `x >= 1`, where
`f_omega x = 2 ↑^(x+1) (x+3)`.  Iteration lemmas compare `round` and
`f_omega` symbolically.  The chain formalised here is:

* `Nat.iter 3 f_omega 14 < m2` (the initial three rounds plus the first epoch);
* if `x < Nat.iter K round 6`, then `f_omega1 x < next (Nat.iter K round 6)`;
* applying that three times gives
  `f_omega1^3(f_omega^3 14) < m5 < sigma`.

## Machine-checked statements

| theorem | file | statement |
| --- | --- | --- |
| `bb83_halts` | `BB83_run.v` | `halts tm c0` |
| `reaches_final` | `BB83_run.v` | `c0 -->* c_final` |
| `final_halted` | `BB83_run.v` | `halted tm c_final` (`F2 = 1RZ`) |
| `fomega1_iter3_lt_sigma` | `BB83_score.v` | `f_omega1^3(f_omega^3 14) < sigma` |
| `bb83_main` | `BB83_score.v` | all of the above, with `sigma = 2*mfin+7` |

The clean build reports 9 main statements closed under the global context and
no axioms.
