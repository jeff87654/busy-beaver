# BB(7,4)

A 7-state, 4-symbol machine

    3RD1LE2RA1LF_0LE2LE2RB2RD_1RF1RC2RB0LB_0RC0LD3RC2RA_1RC2LE1LG2RF_0LA0LD3LG1RZ_1LD2RA2LG0RB

found by loader3229.  This directory contains a complete, **axiom-free
Coq/busycoq proof** that it halts from the blank tape.  The proof certifies

    sigma = 2 * mfin + 7
    f_(omega+3)(21) < sigma .

The mathematical write-up is in
[3RD1LE2RA1LF_0LE2LE2RB2RD_1RF1RC2RB0LB_0RC0LD3RC2RA_1RC2LE1LG2RF_0LA0LD3LG1RZ_1LD2RA2LG0RB.md](3RD1LE2RA1LF_0LE2LE2RB2RD_1RF1RC2RB0LB_0RC0LD3RC2RA_1RC2LE1LG2RF_0LA0LD3LG1RZ_1LD2RA2LG0RB.md);
the Coq development is in [verify/](verify/).

## Main results

| theorem | file | statement |
| --- | --- | --- |
| `bb74_halts` | `BB74_run.v` | `halts tm c0` — the machine halts from the blank tape |
| `reaches_final` | `BB74_run.v` | `c0 -->* c_final`, where state F reads the final 3 |
| `final_halted` | `BB74_run.v` | `halted tm c_final` — the configuration with `F3 = 1RZ` |
| `fomega3_21_lt_sigma` | `BB74_score.v` | `f_omega3 21 < sigma`, i.e. `f_(omega+3)(21) < sigma` |
| `bb74_main` | `BB74_score.v` | all of the above, with `sigma = 2 * mfin + 7` |
| `B_rule`, `rule2`, `rule3a`, `rule3b`, `rule3c`, `halt_from_B` | `BB74_rules.v` | the BB34-style descent and BB74's tail rules |
| `g_closed`, `round_closed`, `round_gt_fomega` | `BB74_score.v` | Knuth closed forms and the one-round lower bound |

Here `f_omega n = 2 ↑^(n+1) (n+3)`, `f_omega1 n = f_omega^n n`,
`f_omega2 n = f_omega1^n n` and `f_omega3 n = f_omega2^n n`, so
`f_omega3 = f_(omega+3)`.  `sigma = 2*mfin+7`, where `mfin = m24` is sealed
behind a `sig` in `BB74_run.v`:

    m1  = round^2(6)
    m2  = next m1,  m3 = next m2
    m4  = gamma m3, ..., m24 = gamma m23       (21 gamma steps)
    next m  = round^(2m+2)(6)
    gamma m = next^(2m+3)(round^2 6)
    round m = desc (2m+2) (g_(2m+2)(0))

**No large number is ever evaluated.**  `mfin`, `m1`…`m24`, `next`, `gamma`
and `round` are opaque; all Knuth expressions are manipulated symbolically.

## Build

    cd verify
    BUSYCOQ=D:/busycoq/verify ./compile_clean.sh

Needs Coq 8.20.1 and a busycoq checkout (commit `bd2e36f`) with the seven
needed `.v` files compiled first.  The script compiles

    BB74.v → Individual74.v → BB74_rules.v → BB74_start.v → BB74_run.v → BB74_score.v

and then `probe.v`, writing `compile_clean.log` and `probe.log`.  The probe must
report no axioms.

## Layout

    README.md                                                                                                                             this file
    3RD1LE2RA1LF_0LE2LE2RB2RD_1RF1RC2RB0LB_0RC0LD3RC2RA_1RC2LE1LG2RF_0LA0LD3LG1RZ_1LD2RA2LG0RB.md                                     the mathematical write-up
    verify/                                                                                                                               the Coq development
    tools/                                                                                                                                simulator, rule checker and chunk generator

## Status

The clean build succeeds: all six development files and `probe.v` compile from
scratch; `probe.log` reports the main statements *closed under the global
context* and contains no `Axioms:` line.
