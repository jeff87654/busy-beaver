# BB(7,3)

A 7-state, 3-symbol machine

    2RD1LE2RA_0LE2LE2RB_1RF1RC2RB_0RC0LG1LD_1RC2LE1LG_1RG0LA1RZ_1LD2RA2LG

with a complete, **axiom-free Coq/busycoq proof** that it halts from the blank
tape.
Found by loader3229 on 2026-11-17.
Its sigma score satisfies

    f_(omega+1)(11) < sigma .

The mathematical write-up is in
[2RD1LE2RA_0LE2LE2RB_1RF1RC2RB_0RC0LG1LD_1RC2LE1LG_1RG0LA1RZ_1LD2RA2LG.md](2RD1LE2RA_0LE2LE2RB_1RF1RC2RB_0RC0LG1LD_1RC2LE1LG_1RG0LA1RZ_1LD2RA2LG.md);
the Coq development is in [verify/](verify/).

## The main results

| theorem | file | statement |
| --- | --- | --- |
| `bb73_halts` | `BB73_run.v` | `halts tm c0` — the machine halts from the blank tape |
| `reaches_final` | `BB73_run.v` | `c0 -->* c_final`, where `c_final` is state F reading the final 2 after `1^(2*mfin+4)` |
| `final_halted` | `BB73_run.v` | `halted tm c_final` — the configuration with `F2 = 1RZ` |
| `fomega1_lt_sigma` | `BB73_score.v` | `f_omega1 11 < sigma`, i.e. **σ > f_(ω+1)(11)** |
| `bb73_main` | `BB73_score.v` | all of the above, with `sigma = 2 * mfin + 5` |
| `B_rule` | `BB73_rules.v` | `B(k,n,m) r -->* B(k,0,g_(k-1)^n(m)) r` — the BB34-style main rule |
| `rule2`, `rule3`, `halt_from_B` | `BB73_rules.v` | the BB73-specific tail rules |
| `g_closed` | `BB73_score.v` | `2 g_(k+1)(m) + 4 = 2 ↑^k (2m+4)` |

Here `f_omega n = 2 ↑^(n+1) (n+3)` and `f_omega1 n = f_omega^n n`; this is the
usual Knuth-arrow normal form of `f_(ω+1)(n)`.  `sigma = 2*mfin+5`, where

    mfin = round^12(1)
    round m = desc (2m+2) (g_(2m+2)(0))

is the parameter produced by the twelve rounds of the tail automaton.

**No large number is ever evaluated.**  `mfin` is sealed behind a `sig`;
`round` and `f_omega` become opaque before the iteration argument; and every
Knuth expression is manipulated by rewriting only.  This follows the same
precautions as BB34's `g15`.

## Build

    cd verify
    BUSYCOQ=D:/busycoq/verify ./compile_clean.sh

Needs Coq 8.20.1 and a busycoq checkout (commit `bd2e36f`) with the seven
needed `.v` files in `verify/` compiled first.  The script compiles

    BB73.v → Individual73.v → BB73_rules.v → BB73_start.v → BB73_run.v → BB73_score.v

and then `probe.v`, writing `compile_clean.log` and `probe.log`.  The probe must
report no axioms.

## Layout

    README.md                                                       this file
    2RD1LE2RA_..._1LD2RA2LG.md                                      the mathematical write-up
    verify/                                                         the Coq development
    tools/                                                          simulator, rule checker and chunk generator

## Status

**Complete.**  All six development files and `probe.v` compile from scratch;
`probe.log` reports 9 main statements *closed under the global context* and
contains no `Axioms:` line.
