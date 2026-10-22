# Coq proofs for `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA` (C7)

This directory is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). **To check the claims, read `c7/Defs.v`, `c7/Statement.v` and the two theorems at the end of
`c7/Lower5.v`**, together with busycoq's `TM.v`. These state every result in terms of `Defs.v` and busycoq only, and
`Statement.v` pins the table against the machine string through a parser of the literal string. `probe.v` runs
`Print Assumptions` on each theorem.

For C7 (H1 undefined: the halt) it proves, with no axioms:

- `Statement.c7_halts : halts tm7 c0`;
- `Lower5.c7_lower5`: every halted configuration c reached from the blank tape has N ones with
  `f_omega (f_omega (f_omega (f_omega (f_omega (2 * arrow 13 2 3))))) < N`;
- `Lower5.c7_lower6_12`: the same N satisfies `f_omega (f_omega (f_omega (f_omega (f_omega (f_omega 12))))) < N`;
- `Statement.c7_lower`: the same N satisfies `f_omega (f_omega (f_omega (f_omega (6 * arrow 13 2 3 + 3)))) < N` (the
  first bound proved; `Lower5.v` starts the f_omega levels one clear earlier);
- `Statement.c7_beats_m8_bound`: the same N satisfies `f_omega (f_omega (6 * arrow 13 2 3 + 3)) < N`. This constant
  is the upper bound of the BB(8) entry M8 (`../../BB8/verify_m8/`, `Statement.m8_bracket`), so C7's score is above M8's;
- `Statement.c7_table`: `tm7` is the parse of the string `"1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA"`.

The machine, the run and the proof are described in
[`../1RB0RA_..._0LI---_1LC0RA.md`](../1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA.md).

## How the proof is organised

The proof runs on an auxiliary 11-state machine X' and transfers to C7 by a simulation.

    C04 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF                (../verify_c04)
    X   = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LJ0LC_0RG1LD_0LH1LH_1RI---_0RI0RF_0LK---_0RC1RH    (../verify_f3, f3_0RC)
    X'  = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LJ0LC_0RG1LD_0LH1LH_1RI---_0RI0RF_0LK---_1LC0RA    (dev/Base.v)

X' is C04 with E0 = 1LJ, J = 0LK / halt and K = 1LC / 0RA, which is C7's state I. C7 changes M8's behaviour at every
exhaustion, so, unlike f3_0RC's proof, this one cannot reuse C04's cascade and endgame lemmas. It reuses only the
champion rules, the token layer with its clears and the first 2369 steps, and the cascade moment `D0f`. Every
exhaustion of C7 has its own generated lemma, and C7's cascade, its counter and its halting branch are proved here.

`c7/Sim.v` relates C7 to X'. Its state map is A..F → A..F, G → I, H → J, I → K. C7's F0 = 1RG takes three X' steps (F0,
G, H0), and every other step is one X' step. C7 halts exactly where X' does, on the same tape.

## Files

Logical paths: `lib/` = `XL`, `lib9/` = `BB8` (the name `../verify_c04/lib` uses for the same two files), `dev/` =
`XDev`, `score/` = `XScore`, `c7/` = `C7`. "Generated" files were written by the symbolic executor of C04's development,
run on X' and counting raw X' steps. Each has one lemma per phase of the run, with the run lengths as variables, and is
proved by stepping the machine and by induction for each repeated block.

| file | content |
|---|---|
| `lib/BB112.v`, `lib/Individual112.v` | busycoq instantiated for 11 states; identical to `../verify_f3/lib/` |
| `lib9/BB92.v`, `lib9/Individual92.v` | busycoq instantiated for 9 states (C7); byte-identical to `../verify_c04/lib/` |
| `dev/Base.v` | X''s table and C04's tape normalisation; `../verify_f3/dev/Base.v` with K's row changed |
| `dev/G_rules.v`, `dev/Abs.v`, `dev/Lift.v` | port of `../verify_c04`: the champion rules, the token family `Kt`/`Kg`, the clears `CDP`, `U`, the arrows, `Bx`, the first 2369 steps; the cascade moment `D0f` |
| `dev/KStep.v` | the generic part of `../verify_f3/dev/Step.v`: tokens with any far end (`Kx`, `Kgx`) and the clear `CDPx` on them |
| `dev/Res.v` | every accumulator U_j(x), j ≥ 2, is ≡ ρ = 5059528974366 modulo 2^5·3^4·5^14 (`U_res`, `iter_U_res`, `Bx_res`): towers of 2s of height ≥ 20, a Carmichael chain of 16 moduli |
| `dev/C7Arith.v` | generated from the run's linear formulas: every exact division and the residues of the cascade (`c7_arith`) |
| `dev/G_pa1.v`, `dev/G_pa2.v` | generated: exhaustions of types A and C (the far-left loop `PA1`, then `PA2` for n ≡ 1, `PC2` for n ≡ 3 mod 5) |
| `dev/G_pbab.v`, `dev/G_pbc.v` | generated: exhaustions of type B (the single-1 frame, no E0) |
| `dev/G_pd.v`, `dev/G_r30.v`, `dev/G_e2.v`, `dev/G_e3.v` | generated: the exhaustion that starts the counter, the counter's last borrow, its end |
| `dev/G_ent.v` | generated: `ENTRY1`, the cascade entry and its first step (the longest file) |
| `dev/G_sub3.v`, `dev/G_sub0.v`, `dev/G_sub4.v` | generated: C7's cascade steps for L ≡ 3, 0, 4 (mod 5) |
| `dev/G_r2a1.v`, `dev/G_r2pre.v`, `dev/G_r2round.v`, `dev/G_r2vhq.v`, `dev/G_r2vh2b.v` | generated: the r = 2 branch: its first pass, the start of the rounds, one round, the end of the last round, the halt |
| `dev/C7Phases.v`, `dev/C7PhB.v`, `dev/C7Count.v`, `dev/C7Casc.v`, `dev/C7Entry.v` | the generated lemmas restated on tokens; the counter by induction on its rounds |
| `dev/C7Top.v` | the blank tape to the cascade moment at step 9 (`reach_count`, `reach_L9`) |
| `dev/C7Halt.v` | the r = 2 branch: the u rounds by induction (`rounds`), the halting configuration and its ones count |
| `dev/Ones.v` | `ones`, `count1`, `sym_val` for X' configurations (the text of `../verify_f3/k31/K31_Abs.v`) |
| `score/Score.v` | f_k ≤ U_k and `S1_core`; identical to `../verify_f3/score/Score.v` |
| `dev/C7Score.v` | f_ω²(12B + 27) < R₃ and f_ω⁴(12B + 27) < R₅ ≤ R₁₀ along the run |
| `dev/C7Final.v` | `x_goal`: X' halts with N ones and f_ω⁴(12B + 27) < N; `x_halts` |
| `dev/C7Score5.v` | five f_ω levels from the clear after J2 (depth (27B + 33)/5): f_ω⁵(y) < R₅ for y ≤ (27B + 28)/5 (`chain5`); f_(k+2) ≤ U_k, so f_ω(12) ≤ B |
| `dev/C7Final5.v` | `x_goal5`: `x_goal`'s run, verbatim, with f_ω⁵(4B + 8) < N and f_ω⁶(12) < N |
| `c7/Defs.v` | **read this**: `tm7`, `sym_val`, `count1`, `ones`, `iter`, `arrow`, `f`, `f_omega`, `f_w1`. From `(** Counting ones. *)` on, it is the text of `../../BB8/verify_m8/Defs.v` |
| `c7/Sim.v` | the simulation of C7 by X': `stmap`, `Rel`, `c7_halts_of_x`, and the transfer of halting counts |
| `c7/Final7.v` | `c7_halts`, `c7_lower`, `c7_beats_m8_bound`, with pointwise bridges between `Defs.v`'s copies and the development's definitions, proved by reflexivity |
| `c7/Statement.v` | **read this**: `c7_table`, `c7_halts`, `c7_lower`, `c7_beats_m8_bound`, in terms of `Defs.v` and busycoq only |
| `c7/Lower5.v` | **read its last two theorems**: `c7_lower5`, `c7_lower6_12` (transferred from `x_goal5` as in `Final7.v`) |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject`, `port_check.sh` | build script, project file, check of the reused files |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of the from-scratch build and the probe, hashes of the source files |

The `.v` files are those of the development where the proof was written. Only their header comments were edited, to
name this directory instead of the development's folders. `probe.v` also moved from `c7/` to this directory, and it
gained `Print tape0` and one `Print Assumptions` per theorem of `Statement.v`.

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh          # everything (46 files), then probe.v
    BUSYCOQ=/path/to/busycoq/verify J=8 ./compile_clean.sh      # 8 coqc at a time (default 4)
    ./port_check.sh                                             # the reused files against ../verify_c04, ../verify_f3

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo` and
`Flip.vo` built. `COQC` may name a specific `coqc`. The script starts each file as soon as the files it needs are
compiled, the longest files first, and writes per-file coqc output to `_logs/`. `./compile_clean.sh only FILE…` and
`./compile_clean.sh probe` work as in `../verify_c04`.

The from-scratch build here (section "Verification record") took 6,890 s of wall time with 3 coqc at a time on a
shared, heavily loaded laptop, and 6,721 s of CPU time in all. The longest files were `dev/G_ent.v` (2,945 s CPU),
`dev/G_pa2.v` (937 s) and `dev/G_pd.v` (387 s); everything else is under 260 s CPU. The development's builds of
`../verify_f3` ran about 2.5 times slower in CPU time than GitHub's runners, so the CI job (J = 4) should take well
under an hour. Memory: under 3 GB per coqc (`dev/G_ent.v`).

`probe.v`:
- checks by conversion all 18 entries of `tm7` against lines written from the machine string (H1 is `None`), and
  against `Statement.v`'s parser of the literal string (`Statement.c7_table`); prints `c0` and `tape0`;
- prints the definitions the statements use (`ones`, `count1`, `sym_val`, `iter`, `arrow`, `f`, `f_omega`);
- states the three main results as one conjunction `c7_all`, written out with qualified names, and proves it
  (`c7_all_ok`); checks the types of the theorems of `Statement.v`;
- runs `Print Assumptions` on `c7_all_ok` and on each of the four theorems of `Statement.v`;
- states the two bounds of `Lower5.v` as a second conjunction `c7_all5` with qualified names, proves it
  (`c7_all5_ok`), and runs `Print Assumptions` on it and on each of the two theorems.

Expected: `probe.log` contains eight lines `Closed under the global context` and no `Axioms:`.

## Verification record

`compile_clean.log` is from a from-scratch build on 2026-10-22: Coq 8.20.1 (Coq Platform 2025.01), Windows 11, a shared
laptop with other builds running, every coqc at Idle priority. The directory held only the 43 `.v` files, `probe.v`
and the scripts, against busycoq at commit `bd2e36f` with its 7 needed files compiled first. Command:
`BUSYCOQ=… J=3 ./compile_clean.sh`, with `COQC` set to a wrapper that starts coqc at Idle priority. Result: all 43
files compiled (COMPILE DONE, 6,890 s), then the probe of that time (213 s), which reported five results closed under
the global context and no `Axioms:`. `port_check.sh` passed against `../verify_c04` and `../verify_f3`.

Then the three files of the f_ω⁵ bound (`dev/C7Score5.v`, `dev/C7Final5.v`, `c7/Lower5.v`) were added and
compiled on top of that build with `./compile_clean.sh only dev/C7Score5 dev/C7Final5 c7/Lower5` (91 s,
`compile_lower5.log`), and the extended probe was run (`./compile_clean.sh probe`, 485 s). `probe.log` is from that run:
eight results closed under the global context, no `Axioms:`.

`sha256.txt` has the SHA-256 of the 46 `.v` files, `probe.v`, `compile_clean.sh`, `port_check.sh` and `_CoqProject`, as
committed.
