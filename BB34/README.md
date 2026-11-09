# BB(3, 4)

BB(3,4) champion **1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC** (Pavel Kropitz's machine,
analysed by Shawn Ligocki, *BB(3, 4) > Ack(14)*, 2024-05-22): a full **axiom-free Coq
proof** that it halts from the blank tape with

    σ = (2 ↑^15 5) + 14

nonblank symbols on the tape (fifteen Knuth up-arrows).  The write-up of the
mathematics is in
[1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC.md](1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC.md);
the Coq development is in [verify/](verify/).

## The main results

| theorem | file | statement |
| --- | --- | --- |
| `bb34_halts` | `BB34_run.v` | `halts tm c0` — the machine halts from the blank tape |
| `reaches_final` | `BB34_run.v` | `c0 -->* c_final`, where `c_final = Bcfg 16 0 g15 (2 >> const 0)` is state A reading the 2 after `3^(2 g15 + 1) 2^16` |
| `final_halted` | `BB34_run.v` | `halted tm c_final` — that configuration is the halting one (`A2 = 1RZ`) |
| `sigma_eq` | `BB34_score.v` | `sigma = knuth 15 2 5 + 14`, i.e. **σ = (2 ↑^15 5) + 14** |
| `bb34_main` | `BB34_score.v` | all of the above in one statement |
| `B_rule` | `BB34_rules.v` | `B(k,n,m) R -->* B(k,0,g_(k-1)^n(m)) R` — Ligocki's Theorem 3, proved by double induction |
| `g_closed` | `BB34_score.v` | `2 g_(k+1)(m) + 4 = 2 ↑^k (2m+4)` — the closed form of the `g` hierarchy |
| `g_iter_closed` | `BB34_score.v` | `2 g_k^n(0) + 4 = 2 ↑^k (n+2)` |

`knuth n a b` is Knuth's `a ↑^n b` with `a ↑^0 b = a·b` and `a ↑^(n+1) b = (a ↑^n b)^b 1`.

**No large number is ever evaluated.**  `g 15` unfolds to an exponentially large term
(`g 15 x` iterates `g 14` `2x+2` times, so normalising it also normalises its argument),
and `2 ↑^15 5` is beyond any arithmetic.  Both are kept symbolic: `g15` is sealed behind
a `sig` so that no tactic can evaluate it, and `knuth 15 2 5` is only ever manipulated by
rewriting.  See [verify/coq_quirks.md](verify/coq_quirks.md) for the details.

## Build

    cd verify
    BUSYCOQ=../busycoq/verify ./compile_clean.sh

Needs Coq 8.20.1 and a busycoq checkout (commit `bd2e36f`); the seven busycoq `verify/`
files needed are included in [busycoq/](busycoq/).  The whole build takes about 40 s on a
modern laptop.  See [verify/README.md](verify/README.md) for details.

## Layout

    README.md                                       this file
    1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC.md      the mathematical write-up
    verify/                                         the Coq development
    busycoq/                                        the busycoq files the proof depends on
    tools/sim.py                                    a small Python simulator (cross-check)
    tools/gen_start.py                              generator for verify/BB34_start.v

## Status

**Complete.**  `BB34.v`, `Individual34.v`, `BB34_rules.v`, `BB34_start.v`, `BB34_run.v`,
`BB34_score.v` and `probe.v` all compile from scratch on Coq 8.20.1, and `probe.v` reports
that all 24 of the theorems it checks are *closed under the global context* — that is, the
proof uses no axioms at all.
