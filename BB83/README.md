# BB(8,3)

An 8-state, 3-symbol machine

    2LH1LE2RA_0LE2LE2RB_1RF1RC2RB_0RC0LD0RH_1RC2LE1LG_0LA0LD1RZ_1LD2RA2LG_2RD1LF1LG

found by loader3229, based on the BB(7,3) champion.  This directory contains a
complete, **axiom-free Coq/busycoq proof** that it halts from the blank tape.
The proof certifies

    sigma = 2 * mfin + 7
    f_(omega+1)^3 ( f_omega^3(14) ) < sigma .

The mathematical write-up is in
[2LH1LE2RA_0LE2LE2RB_1RF1RC2RB_0RC0LD0RH_1RC2LE1LG_0LA0LD1RZ_1LD2RA2LG_2RD1LF1LG.md](2LH1LE2RA_0LE2LE2RB_1RF1RC2RB_0RC0LD0RH_1RC2LE1LG_0LA0LD1RZ_1LD2RA2LG_2RD1LF1LG.md);
the Coq development is in [verify/](verify/).

## Main results

| theorem | file | statement |
| --- | --- | --- |
| `bb83_halts` | `BB83_run.v` | `halts tm c0` — the machine halts from the blank tape |
| `reaches_final` | `BB83_run.v` | `c0 -->* c_final`, where state F reads the final 2 |
| `final_halted` | `BB83_run.v` | `halted tm c_final` — the configuration with `F2 = 1RZ` |
| `fomega1_iter3_lt_sigma` | `BB83_score.v` | `f_omega1^3(f_omega^3 14) < sigma` |
| `bb83_main` | `BB83_score.v` | all of the above, with `sigma = 2 * mfin + 7` |
| `B_rule`, `rule2`, `rule3a`, `rule3b`, `halt_from_B` | `BB83_rules.v` | the BB34-style descent and BB83's tail rules |
| `g_closed`, `round_closed`, `round_gt_fomega` | `BB83_score.v` | Knuth closed forms and the one-round lower bound |

Here `f_omega n = 2 ↑^(n+1) (n+3)` and `f_omega1 n = f_omega^n n`; this is the
same notation as the BB73 development.  `sigma = 2*mfin+7`, where `mfin = m5`
is sealed behind a `sig` in `BB83_run.v`:

    m1 = round^3(6)
    m2 = next m1,  m3 = next m2,  m4 = next m3,  m5 = next m4
    next m = round^(2m+2)(6)
    round m = desc (2m+2) (g_(2m+2)(0))

**No large number is ever evaluated.**  `mfin`, `m1`…`m5`, `next` and `round`
are opaque; all Knuth expressions are manipulated symbolically.

## Build

    cd verify
    BUSYCOQ=D:/busycoq/verify ./compile_clean.sh

Needs Coq 8.20.1 and a busycoq checkout (commit `bd2e36f`) with the seven
needed `.v` files compiled first.  The script compiles

    BB83.v → Individual83.v → BB83_rules.v → BB83_start.v → BB83_run.v → BB83_score.v

and then `probe.v`, writing `compile_clean.log` and `probe.log`.  The probe must
report no axioms.

## Layout

    README.md                                                                                 this file
    2LH1LE2RA_..._2RD1LF1LG.md                                                                  the mathematical write-up
    verify/                                                                                     the Coq development
    tools/                                                                                      simulator, rule checker and chunk generator

## Status

The clean build succeeds: all six development files and `probe.v` compile from
scratch; `probe.log` reports 9 main statements *closed under the global
context* and contains no `Axioms:` line.
