# BB(3, 5)

BB(3,5) champion **1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC**: a full
**axiom-free Coq proof** that it halts from the blank tape and that the number of non-blank
cells on the final tape satisfies

    σ  >  f_ω(2 ↑^15 5)

where `2 ↑^15 5` is 2 with fifteen Knuth up-arrows applied to 5 and `f_ω(n) = 2 ↑^(n+1) (n+3)`
is the omega-th element of the fast-growing hierarchy in arrow normal form.  The write-up of
the mathematics is in
[1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC.md](1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC.md);
the Coq development is in [verify/](verify/).

## The main results

| theorem | file | statement |
| --- | --- | --- |
| `bb35_halts` | `BB35_run.v` | `halts tm c0` — the machine halts from the blank tape |
| `reaches_final` | `BB35_run.v` | `c0 -->* c_final`, where `c_final = ([3]^^(2 * mfin + 3) *> const 0) {{B}}> (4 >> const 0)` is state B reading the 4 after the block of threes |
| `final_halted` | `BB35_run.v` | `halted tm c_final` — that configuration is the halting one (`B4 = 1RZ`) |
| `sigma_closed` | `BB35_score.v` | `sigma = aw 0 (2 * g15 + 16) 4`, the nested Knuth expression `2 ↑^0 (2 ↑^1 (… (2 ↑^(2g15+15) 4) …))` |
| `sigma_gt_fomega` | `BB35_score.v` | `f_ω(K) < sigma` with `K = 2 ↑^15 5` |
| `fomega_lt_sigma` | `BB35_score.v` | `f_omega (knuth 15 2 5) < sigma`, i.e. **σ > f_ω(2 ↑^15 5)** |
| `bb35_main` | `BB35_score.v` | all of the above in one statement |
| `B_rule` | `BB35_rules.v` | `B(k,n,m) R -->* B(k,0,g_(k-1)^n(m)) R` — Ligocki's Theorem 3, proved by double induction |
| `rule1` | `BB35_rules.v` | `B(k,0,m) 2 -->* B(k+2m+1,0,0) 4` |
| `rule2` | `BB35_rules.v` | `B(k,0,m) 4 -->* B(k-1,2m+2,0) 4` (k ≥ 2) |
| `rule3` | `BB35_rules.v` | `B(1,0,m) 4 -->* 3^(2m+3) B> 4`, and then the machine halts |
| `g_closed` | `BB35_score.v` | `2 g_(k+1)(m) + 4 = 2 ↑^k (2m+4)` — the closed form of the `g` hierarchy |
| `g_iter_closed` | `BB35_score.v` | `2 g_k^n(0) + 4 = 2 ↑^k (n+2)` |

`knuth n a b` is Knuth's `a ↑^n b` with `a ↑^0 b = a·b` and `a ↑^(n+1) b = (a ↑^n b)^b 1`.

**No large number is ever evaluated.**  `g 15` unfolds to an exponentially large term
(`g 15 x` iterates `g 14` `2x+2` times, so normalising it also normalises its argument),
and `2 ↑^15 5` is beyond any arithmetic.  Both are kept symbolic: `g15` is made `Opaque`
so that no tactic can evaluate it, and `knuth 15 2 5` is only ever manipulated by
rewriting.  See [verify/coq_quirks.md](verify/coq_quirks.md) for the details.

## Build

    cd verify
    BUSYCOQ=D:/busycoq/verify ./compile_clean.sh

Needs Coq 8.20 and a busycoq checkout (the one in `D:/busycoq`).  The whole build takes about
30 s.  See [verify/README.md](verify/README.md) for details.

## Layout

    README.md                                       this file
    1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC.md      the mathematical write-up
    verify/                                         the Coq development
    tools/                                          Python simulators / macro scanners (cross-check)

## Status

**Complete.**  `BB35.v`, `Individual35.v`, `BB35_rules.v`, `BB35_start.v`, `BB35_run.v`,
`BB35_score.v` and `probe.v` all compile from scratch on Coq 8.20, and `probe.v` reports that
all 35 of the theorems it checks are *closed under the global context* — that is, the proof
uses no axioms at all.

Note that the wiki's `> f_ω(2 ↑^15 5)` is a bound on the **runtime**; the bound proved here is
on the **space** (σ), which is what was requested.  The runtime bound is not proved (the steps
of the macro phases are not enumerated).
