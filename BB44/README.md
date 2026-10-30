# BB(4, 4)

BB(4,4) champion **0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA**: a full
**axiom-free Coq proof** that it halts from the blank tape with

    σ = (2 ↑^509 3) + 510

nonblank symbols on the tape (509 Knuth up-arrows), and therefore with
**σ > 2 ↑^509 3**.  The write-up of the mathematics is in
[0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA.md](0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA.md);
the Coq development is in [verify/](verify/).

The proof follows the same route as the BB(3,4) development in
[`../BB34`](../BB34): Ligocki's configuration family `B(k,n,m)`, his descent
rule `B_rule`, and the closed form of the `g` hierarchy.  The BB(4,4) champion
differs from the BB(3,4) one only in `A0`, `B0` and the extra state `D`, so the
descent itself ports over unchanged — but the machine only *reaches* the
descent after two BB(4,4)-specific phases, which are proved here as well
(`B_phase` and `D_phase`).

## The main results

| theorem | file | statement |
| --- | --- | --- |
| `bb44_halts` | `BB44_run.v` | `halts tm c0` — the machine halts from the blank tape |
| `reaches_final` | `BB44_run.v` | `c0 -->* c_final`, where `c_final = Bcfg 510 0 g509 (2 1 3 0^inf)` is state A reading the 2 after `3^(2 g509 + 1) 2^510` |
| `final_halted` | `BB44_run.v` | `halted tm c_final` — that configuration is the halting one (`A2 = 1RZ`) |
| `sigma_eq` | `BB44_score.v` | `sigma = knuth 509 2 3 + 510`, i.e. **σ = (2 ↑^509 3) + 510** |
| `bb44_main` | `BB44_score.v` | all of the above in one statement |
| `B_rule` | `BB44_rules.v` | `B(k,n,m) R -->* B(k,0,g_(k-1)^n(m)) R` — Ligocki's Theorem 3, proved by double induction |
| `B_phase` | `BB44_rules.v` | `B(2,0,m) 0^inf -->* B(1,2m+2,0) 0^inf` — the BB(4,4)-specific phase B |
| `D_phase` | `BB44_rules.v` | `B(1,0,m) 0^inf -->* B(2m+2,1,0) 2 1 3 0^inf` — the BB(4,4)-specific phase D |
| `g_closed` | `BB44_score.v` | `2 g_(k+1)(m) + 4 = 2 ↑^k (2m+4)` — the closed form of the `g` hierarchy |
| `g_iter_closed` | `BB44_score.v` | `2 g_k^n(0) + 4 = 2 ↑^k (n+2)` |

`knuth n a b` is Knuth's `a ↑^n b` with `a ↑^0 b = a·b` and `a ↑^(n+1) b = (a ↑^n b)^b 1`.

**No large number is ever evaluated.**  `g 509` unfolds to an exponentially large term
(`g 509 x` iterates `g 508` `2x+2` times, so normalising it also normalises its argument),
and `2 ↑^509 3` is beyond any arithmetic.  Both are kept symbolic: `g509` is sealed behind
a `sig` so that no tactic can evaluate it, and `knuth 509 2 3` is only ever manipulated by
rewriting.  See [verify/coq_quirks.md](verify/coq_quirks.md) for the details.

## The run

    0^inf A> 0^inf  -(98 steps)->  B(2, 6, 0)  0^inf
        ->  B(2, 0, 126)  0^inf                (B_rule, k = 1)
        ->  B(1, 254, 0)  0^inf                (phase B)
        ->  B(1, 0, 254)  0^inf                (B_rule, k = 0)
        ->  B(510, 1, 0)  2 1 3 0^inf          (phase D)
        ->  B(510, 0, g_509(0))  2 1 3 0^inf  (B_rule, k = 509)
        -(A2 = 1RZ)->  0^inf 3^(2 g_509(0)+1) 2^510 1 Z> 1 3 0^inf .

## Build

    cd verify
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

Needs Coq 8.20.1 and a busycoq checkout (commit `bd2e36f`), whose seven needed
`verify/` files must be compiled first.  The whole build takes about 20 s.
See [verify/README.md](verify/README.md) for details.

## Layout

    README.md                                       this file
    0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA.md   the mathematical write-up
    verify/                                         the Coq development
    tools/sim.py                                    a small Python simulator
    tools/check.py                                  cross-check of the start and of the two phases
    tools/gen_start.py                              generator for verify/BB44_start.v

## Status

**Complete.**  `BB44.v`, `Individual44.v`, `BB44_rules.v`, `BB44_start.v`, `BB44_run.v`,
`BB44_score.v` and `probe.v` all compile from scratch on Coq 8.20.1, and `probe.v` reports
that all 32 of the theorems it checks are *closed under the global context* — that is, the
proof uses no axioms at all.
