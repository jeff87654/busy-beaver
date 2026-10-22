# Coq proofs for `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF` (f3_0RC)

This directory is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). **To check the claims, read `f3/Defs.v` and `f3/Statement.v`** (with busycoq's `TM.v`): `Statement.v`
states every result in terms of `Defs.v` and busycoq only, and pins the table against the machine string through a
parser of the literal string. `probe.v` runs `Print Assumptions` on each theorem.

For f3_0RC (H1 undefined: the halt) it proves, with no axioms:

- `Statement.f3_halts : halts tm3 c0`;
- `Statement.f3_beats_m8_bound`: every halted configuration c reached from the blank tape has N ones with
  `f_omega (f_omega (6 * arrow 13 2 3 + 3)) < N`. This constant is the upper bound of the BB(8) entry M8
  (`../../BB8/verify_m8/`, `Statement.m8_bracket`: every halting count of M8 is below it), so f3_0RC's score is above
  M8's, whichever way M8's run ends;
- `Statement.f3_lower`, more precisely: the same N satisfies
  `f_omega (f_omega (6 * iter (arrow 13 2 3 - 5) (arrow 6 2) (iter 4 (arrow 5 2) 4) - 14)) < N`;
- `Statement.f3_table`: `tm3` is the parse of the string `"1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF"`.

The machine, the run and the proof are described in
[`../1RB0RA_..._0LI---_0RC1RF.md`](../1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF.md).

## How the proof is organised

The proof runs on an auxiliary 11-state machine X and transfers to f3_0RC by a simulation.

    C04 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF                (../verify_c04)
    X   = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LJ0LC_0RG1LD_0LH1LH_1RI---_0RI0RF_0LK---_0RC1RH    (dev/Base.v)

X is C04 with E0 = 1LH replaced by a look at the cell left of H. E0 = 1LJ, and J1 is the halt (C04's H1). J0 = 0LK
steps left, and K1 = 1RH returns to H on C04's tape, so these three X steps are C04's one E0 step. K0 = 0RC is
f3_0RC's I0 = 0RC, the only new behaviour. It fires when the cell left of H is blank, which happens at the two
top-level exhaustions. `dev/Base.v` redefines the tactic `step` as one C04 step, that is, three X steps across E0, J0
and K1. So C04's generated proof scripts (`do n step`, `execute`, `follow`) compile unchanged on X. 31 files are C04's
with only mechanical renames (`port_check.sh` checks this), five are lightly edited, and six are new.

`f3/Sim.v` relates f3_0RC to X. Its state map is A..F → A..F, G → I, H → J, I → K. f3's F0 = 1RG takes three X steps
(F0, G, H0), and f3's I1 = 1RF is X's K1 = 1RH followed by H0. f3_0RC halts exactly where X does, on the same tape.

## Files

Logical paths: `lib/` = `XL`, `lib9/` = `BB8` (the name `../verify_c04/lib` uses for the same two files), `dev/` =
`XDev`, `k31/` = `XK31`, `score/` = `XScore`, `f3/` = `F3`. "Port" means the file of `../verify_c04` with the same name,
changed only by the renames that `port_check.sh` re-applies.

| file | content |
|---|---|
| `lib/BB112.v`, `lib/Individual112.v` | busycoq instantiated for 11 states (the machine X) |
| `lib9/BB92.v`, `lib9/Individual92.v` | busycoq instantiated for 9 states (f3_0RC); byte-identical to `../verify_c04/lib/` |
| `dev/Base.v` | edited from C04's: X's table, and `step` = one C04 step |
| `dev/G_rules.v`, `dev/G_sub2.v` … `dev/G_sub5.v`, `dev/G_stop.v`, `dev/G_entry.v`, `dev/G_end.v`, `dev/G_p14_0.v` … `dev/G_p14_5.v`, `dev/G_p20_0.v` … `dev/G_p20_5.v` | port: C04's generated machine lemmas (champion rules, cascade sub-steps, stop, entry, class-b tail and prefixes) |
| `k31/K_rf.v`, `k31/K_x.v`, `k31/K_e1.v`, `k31/K_e2.v` | port: C04's generated key-31 endgame lemmas |
| `dev/Abs.v`, `dev/Lift.v`, `dev/Orbit.v`, `dev/Cascade.v`, `dev/CBtail.v`, `k31/K31_Abs.v`, `k31/K31_Mach.v` | port: tokens, clears, the cascade moment `D0f`, the orbit map and its parity, the cascade induction, the key-31 abstractions |
| `dev/Step.v`, `dev/Fin.v`, `dev/Endgame.v`, `k31/K31_End.v`, `score/Score.v` | edited from C04's: C04's own top level removed, and the cascade start (`Pm`, `L1`) made a parameter |
| `dev/G_xreb1.v` | new, generated: `XREB1`, exhaustion #1 (top level, through K0), parametric in B |
| `dev/G_xreb2.v` | new, generated: `XREB2`, the rebuild that follows the first clear (no E0 inside), parametric in the accumulator |
| `dev/G_xtop.v` | new, generated: `XTOPENTRY` (exhaustion #2, top level, through K0) and `XTOP1` (its first cascade sub-step) |
| `dev/XTop.v` | new: the phases P1–P3 on tokens (`xreb1`, `clears1`, `xreb2`, `clear2`, `xte`, `xt1`), the residues (`U_mod50`: every accumulator is 16 mod 50), and `reach_topX`: the blank tape reaches the cascade at an odd start ≡ 1 (mod 3) |
| `dev/XFinal.v` | new: `x_halts`, C04's cascade and endgame applied from `reach_topX` |
| `dev/XScore.v` | new, adapted from C04's `ScoreEnd.v`: every halting count N of X satisfies `f_omega (f_omega a) < N` for every a ≤ 12R'' + 10 |
| `f3/Defs.v` | **read this**: `tm3`, `sym_val`, `count1`, `ones`, `iter`, `arrow`, `f`, `f_omega`, `f_w1`. From `(** Counting ones. *)` on, it is the text of `../../BB8/verify_m8/Defs.v` |
| `f3/Sim.v` | the simulation of f3_0RC by X: `stmap`, `Rel`, `f3_halts_sim`, and the transfer of halting counts |
| `f3/Final3.v` | `f3_halts`, `f3_lower`, `f3_beats_m8_bound`; `Rpp_explicit` (2R'' + 4 as an iterate of Knuth arrows) and `m8_le` (6 · 2↑^13 3 + 3 ≤ 12R'' + 10); pointwise bridges between `Defs.v`'s copies and the development's definitions, by reflexivity |
| `f3/Statement.v` | **read this**: the four theorems above, in terms of `Defs.v` and busycoq only |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject`, `port_check.sh` | build script, project file, port check |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of the from-scratch build and the probe, hashes of the source files |

The `.v` files are those of the development where the proof was written, unchanged, with two exceptions. `probe.v`
moved from `f3/` to this directory and gained `Print tape0` and one `Print Assumptions` per theorem of `Statement.v`.
The header comment of `f3/Statement.v` was updated.

The development also had a file comparing f3_0RC's count directly with M8's and C04's compiled Coq statements
(`f3_beats_m8`, `f3_beats_c04`, compiled there against a byte-identical build of `../verify_c04` and
`../../BB8/verify_m8`). It is not included here. Building it needs the C04 tree, `../../BB8/verify` and
`../../BB8/verify_m8` in the same build as this one, which is too long for one CI job. That comparison is the chain of
two theorems. `Statement.m8_bracket` in `../../BB8/verify_m8` puts M8's count below
`f_omega (f_omega (6 * arrow 13 2 3 + 3))`, and `f3_beats_m8_bound` here puts f3_0RC's count above it. The two
`Defs.v` define `f_omega` and `arrow` with the same text, which CI checks by `diff`.

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh          # everything, then probe.v
    BUSYCOQ=/path/to/busycoq/verify J=8 ./compile_clean.sh      # 8 coqc at a time (default 4)
    ./port_check.sh                                             # the ported files against ../verify_c04

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo` and
`Flip.vo` built. COQC may name a specific `coqc`. The script starts each file as soon as the files it needs are
compiled, the longest files first, and writes per-file coqc output to `_logs/`. `./compile_clean.sh only FILE…` and
`./compile_clean.sh probe` work as in `../verify_c04`.

The whole build is about 8.9 CPU-hours on our machine (Idle priority), close to C04's: the generated files are C04's,
and the redefined `step` adds little. The longest files are `k31/K_e1.v` (8016 s of CPU), `dev/G_sub2.v` (4098 s) and
`k31/K_e2.v` (2638 s). The GitHub workflow (`.github/workflows/coq.yml`, job `bb9-f3`) runs `port_check.sh`, checks
that `f3/Defs.v` has the definitions of `../../BB8/verify_m8/Defs.v` (by `diff`), and runs `compile_clean.sh` with
J = 4 whenever these files or `../verify_c04` change (and weekly). It fails unless all 51 `.vo` files are built and
`probe.log` reports five results closed under the global context and no `Axioms:`. Memory: under 1 GB per coqc.

`probe.v`:
- checks by conversion all 18 entries of `tm3` against lines generated from the machine string (H1 is `None`), and
  against `Statement.v`'s parser of the literal string (`Statement.f3_table`); prints `c0` and `tape0`;
- prints the definitions the statements use (`ones`, `count1`, `sym_val`, `iter`, `arrow`, `f`, `f_omega`);
- states the three main results as one conjunction `f3_all`, written out with qualified names, and proves it
  (`f3_all_ok`); checks the types of the theorems of `Statement.v`;
- runs `Print Assumptions` on `f3_all_ok` and on each of the four theorems of `Statement.v`.

Expected: `probe.log` contains five lines `Closed under the global context` and no `Axioms:`.

## Verification record

`compile_clean.log` and `probe.log` are from a from-scratch build on 2026-10-21/22 in a fresh checkout: Coq 8.20.1 (Coq
Platform 2025.01), busycoq `bd2e36f`, Windows 11, a shared 16-core machine, J = 3, every coqc at Idle priority. The 51
files took 29851 s of wall time (the machine was busy; 31966 s of CPU in all, probe included), and the probe 1380 s.
The probe reported five results closed under the global context and no `Axioms:`. `sha256.txt` has the SHA-256 of
the `.v` files and the scripts.
