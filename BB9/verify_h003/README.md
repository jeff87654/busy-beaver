# Coq proofs for `1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC` (h003)

This directory is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). **To check the claims, read `h003/Defs.v` and `h003/Statement.v`**, together with busycoq's `TM.v`. They
state every result in terms of `Defs.v` and busycoq only, and `Statement.v` pins the table against the machine string
through a parser of the literal string. `probe.v` runs `Print Assumptions` on each theorem.

For h003 (H1 undefined: the halt) it proves, with no axioms:

- `Statement.h003_halts : halts tmh c0`;
- `Statement.h003_lower`: every halted configuration c reached from the blank tape has N ones with
  `f_omega (f_omega (f_omega (f_omega (f_omega (f_omega (6 * arrow 13 2 3 + 2)))))) < N`;
- `Statement.h003_lower7_12`: the same N satisfies `f_omega (f_omega (f_omega (f_omega (f_omega (f_omega (f_omega 12)))))) < N`;
- `Statement.h003_beats_m8_bound`: the same N satisfies `f_omega (f_omega (6 * arrow 13 2 3 + 3)) < N`. This constant
  is the upper bound of the BB(8) entry M8 (`../../BB8/verify_m8/`, `Statement.m8_bracket`), so h003's score is above
  M8's;
- `Statement.h003_table`: `tmh` is the parse of the string `"1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC"`.

The machine, the run and the proof are described in
[`../1RB0RA_..._0LI---_1RI1RC.md`](../1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC.md).

## How the proof is organised

The proof runs on an auxiliary 11-state machine X3 and transfers to h003 by a simulation.

    C04 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF                (../verify_c04)
    X'  = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LJ0LC_0RG1LD_0LH1LH_1RI---_0RI0RF_0LK---_1LC0RA    (../verify_c7, C7)
    X3  = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LJ0LC_0RG1LD_0LH1LH_1RI---_0RI0RF_0LK---_1RK1RC    (dev/Base.v)

X3 is C04 with E0 = 0LJ, J = 0LK / halt and K = 1RK / 1RC, which are h003's H and I. At an E0 event at cell e whose
cells e − 2 and e + 1 hold 1, C04 runs E0 H0 I1 F1 D0 A1 and X3 runs E0 J0 K1 C0 D0 A1: six steps each, with the same
configuration afterwards. So `dev/Base.v` defines the tactic `step` as one raw X3 step, and C04's generated scripts,
which count raw steps, replay on X3 unchanged wherever their E0 events are of this kind. This holds for the whole of
C04's cascade and endgame, which are therefore reused as they are; only the halting tape changes (X3's E0 writes 0).
h003's own top level (four rebuilding tops and the exit) has new generated lemmas.

`h003/Sim.v` relates h003 to X3. Its state map is A..F → A..F, G → I, H → J, I → K. h003's F0 = 1RG takes three X3
steps (F0, G, H0), and every other step is one X3 step. h003 halts exactly where X3 does, on the same tape.

## Files

Logical paths: `lib/` = `XL`, `lib9/` = `BB8` (the name `../verify_c04/lib` uses for the same two files), `dev/` =
`XDev`, `k31/` = `XK31`, `score/` = `XScore`, `h003/` = `H3`. "Generated" files were written by the symbolic executor of
C04's development, run on X3 and counting raw X3 steps. Each has one lemma per phase of the run, with the run lengths as
variables, and is proved by stepping the machine and by induction for each repeated block. `port_check.sh` checks every
reused file.

| file | content |
|---|---|
| `lib/BB112.v`, `lib/Individual112.v` | busycoq instantiated for 11 states; byte-identical to `../verify_f3/lib/` |
| `lib9/BB92.v`, `lib9/Individual92.v` | busycoq instantiated for 9 states (h003); byte-identical to `../verify_c04/lib/` |
| `dev/Base.v` | X3's table and C04's tape normalisation; `../verify_c7/dev/Base.v` with the rows of E0 and K changed and `step` = one raw step |
| `dev/G_rules.v`, `dev/Abs.v`, `dev/Lift.v`, `dev/Orbit.v`, `dev/Step.v`, `dev/Cascade.v`, `dev/Fin.v`, `dev/Endgame.v` | byte-identical to `../verify_f3/dev/` (C04's port): the champion rules, the token family `Kt`/`Kg`, the clears, `U`, the arrows, `Bx`, the first 2369 steps, the cascade moment `D0f`, the cascade and its endgame (`halts_from_reach`) |
| `dev/G_entry.v`, `dev/G_stop.v`, `dev/G_sub2.v` … `dev/G_sub5.v`, `dev/G_p14_0.v` … `dev/G_p14_5.v`, `dev/G_p20_0.v` … `dev/G_p20_5.v` | generated (C04's): the cascade entry, stop and sub-steps, the class-b endgame; byte-identical to `../verify_f3/dev/` |
| `dev/G_end.v`, `dev/CBtail.v` | `../verify_f3/dev/`'s with X3's halting tape |
| `k31/K_e1.v`, `k31/K_e2.v`, `k31/K_rf.v`, `k31/K31_Abs.v` | generated and abstract files of C04's key-31 endgame; byte-identical to `../verify_f3/k31/` |
| `k31/K_x.v`, `k31/K31_Mach.v`, `k31/K31_End.v` | `../verify_f3/k31/`'s with X3's halting tape (and `K31_End`'s ones bound one lower) |
| `score/Score.v` | f_k ≤ U_k and `S1_core`; byte-identical to `../verify_f3/score/Score.v` |
| `dev/Res.v`, `dev/KStep.v`, `dev/Ones.v`, `dev/G_pbab.v`, `dev/G_pbc.v` | byte-identical to `../verify_c7/dev/`: the tower residue ρ modulo 2^5·3^4·5^14, tokens with any far end and their clear `CDPx`, the ones count, the rebuild without E0 |
| `dev/G_t1_T1a1.v`, `dev/G_t1_T1a2a.v`, `dev/G_t1_YR.v`, `dev/G_t1_YE.v`, `dev/G_t1_T1b.v` | generated: the top for K ≡ 1 (mod 5), with its far-left loop as one round (`YR`) and its end (`YE`) |
| `dev/G_tops_P3.v`, `dev/G_tops_P4.v`, `dev/G_tops_P4b.v` | generated: the exhaustions of the tops for K ≡ 3 and K ≡ 4 (mod 5) |
| `dev/G_tops_TXa.v`, `dev/G_xt1.v` | generated: the exit exhaustion for K ≡ 0 (mod 5) and the first cascade sub-step on a run of 5J + 24 |
| `dev/HPhB.v` | the rebuild without E0 restated on tokens (as `../verify_c7/dev/C7PhB.v`) |
| `dev/HArith.v` | generated from the run's linear formulas: the exact divisions and the branches 4, 3, 1, 1, then the exit (`K4 = 10h + 15`) |
| `dev/HTop.v` | the tops `T1`, `T3`, `T4`, `TX`, the orbit (`orbit_vals`) and `reach_D0_top`: the blank tape reaches the cascade moment |
| `dev/HFinal.v` | `x_halts`: X3 halts (the cascade start `reach_topH`, then `Endgame.halts_from_reach` and `K31_End.k31_end`) |
| `dev/HScore.v` | `x_goal`: X3 halts with N ones and f_ω(f_ω(a)) < N for every a ≤ K₄ − 1 (`../verify_f3/dev/XScore.v` with X3's top) |
| `dev/HGoal.v` | `x_goal6`: f_ω⁶(12B + 26) < N, f_ω⁷(12) < N and f_ω²(12B + 27) < N (`chain4`: one f_ω per rebuilding top; `fw12_le_Bx`) |
| `h003/Defs.v` | **read this**: `tmh`, `sym_val`, `count1`, `ones`, `iter`, `arrow`, `f`, `f_omega`, `f_w1`. From `(** Counting ones. *)` on, it is the text of `../../BB8/verify_m8/Defs.v` |
| `h003/Sim.v` | the simulation of h003 by X3: `stmap`, `Rel`, `h003_halts_of_x`, and the transfer of halting counts (a port of `../verify_c7/c7/Sim.v`) |
| `h003/Final.v` | `h003_halts`, `h003_lower`, `h003_lower7_12`, `h003_beats_m8_bound`, with pointwise bridges between `Defs.v`'s copies and the development's definitions, proved by reflexivity at variable arguments |
| `h003/Statement.v` | **read this**: `h003_table`, `h003_halts`, `h003_lower`, `h003_lower7_12`, `h003_beats_m8_bound`, in terms of `Defs.v` and busycoq only |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject`, `port_check.sh` | build script, project file, check of the reused files |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of the from-scratch build and the probe, hashes of the source files |

The `.v` files are those of the development where the proof was written. Only their header comments were edited, to
name this directory instead of the development's folders, and `probe.v` gained `Print tape0`, the type checks and one
`Print Assumptions` per theorem of `Statement.v`.

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh          # everything (66 files), then probe.v
    BUSYCOQ=/path/to/busycoq/verify J=8 ./compile_clean.sh      # 8 coqc at a time (default 4)
    ./port_check.sh                                             # the reused files against ../verify_c04, _f3, _c7

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo` and
`Flip.vo` built. `COQC` may name a specific `coqc`. The script starts each file as soon as the files it needs are
compiled, the longest files first, and writes per-file coqc output to `_logs/`. `./compile_clean.sh only FILE…` and
`./compile_clean.sh probe` work as in `../verify_c04`.

BUILD_TIMES

`probe.v`:
- checks by conversion all 18 entries of `tmh` against lines written from the machine string (H1 is `None`), and
  against `Statement.v`'s parser of the literal string (`Statement.h003_table`); prints `c0` and `tape0`;
- prints the definitions the statements use (`ones`, `count1`, `sym_val`, `iter`, `arrow`, `f`, `f_omega`);
- states the four main results as one conjunction `h003_all`, written out with qualified names, and proves it
  (`h003_all_ok`); checks the types of the theorems of `Statement.v`;
- runs `Print Assumptions` on `h003_all_ok` and on each of the five theorems of `Statement.v`.

Expected: `probe.log` contains six lines `Closed under the global context` and no `Axioms:`.

## Verification record

BUILD_RECORD
