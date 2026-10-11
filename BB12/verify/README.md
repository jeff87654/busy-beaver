# Coq proofs for `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RK0LC_0RL---_0RF1RZ` (T12a)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (L1 undefined = the halt, `1RZ` in the string; K1 undefined and never read) it proves:

- `BB12_T12a.halt : halts tm c0` -- the machine halts from the blank tape;
- `BB12_T12a_bound.sigma_lower_bound` -- the halting tape holds N ones with
  `F^(2J)(w) <= 6N + 11`, `F w <= 7J + 9`, `w >= F^(2JJ+1)(34)`, `F n = 2↑^n 4`, `JJ = (3T-13)/7`, `T = 2↑^37 3`;
- `BB12_T12a_bound.score_ge_exact` -- `F(F(Wf)) <= 6N + 11`, with `Wf` the BB(10) machine n1's exact final depth
  (an explicit `JJ`-fold recursion of Knuth arrows, printed by the probe);
- `BB12_T12a_bound.beats_n1` -- `N > score_value + 1`, the exact standard score of n1
  (`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC`, `../../BB10/`), against n1's own
  Coq-proved exact score (`BB10_n1_exact.score_closed`);
- `BB12_T12a_fgh.fgh_lower2` -- `f_omega1 (f_omega1 (JJ - 2)) <= 6N + 11`, with the standard fast-growing
  hierarchy of `BB10_n1_fgh.v` (`fgh 0 n = n+1`, `fgh (k+1) n = (fgh k)^n n`, `f_omega n = fgh n n`,
  `f_omega1 n = f_omega^n n`).

The machine halts in state L reading 1, and the halting transition writes 1 on that 1, so the standard score is N.

## Files

| file | content |
|---|---|
| `BB122.v`, `Individual122.v` | busycoq instantiated for 12 states. The state `L` shadows busycoq's direction `L`, so tables write `TM.L` / `TM.R`. |
| `BB12_T12a.v` | the halting proof, 14,268 lines, generated from event specifications. It does not import the n1 files: round 1 (n1's run) is re-proved for the 12-state machine. |
| `BB12_T12a_bound.v` | the score lower bounds and `beats_n1`; imports the halting file unchanged |
| `BB12_T12a_fgh.v` | `fgh_lower2` |
| `BB102.v`, `Individual102.v`, `BB10_n1*.v`, `BB10_lead_*.v`, `BB10_champion_*.v` | the BB(10) n1 development, byte-identical to `../../BB10/verify/multifile/`; used by `beats_n1` and `fgh_lower2` (`BB12_T12a_bound.v` Requires them) |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

This compiles the 16 files in dependency order and then runs `probe.v`. `BB12_T12a.v` takes most of the time:
9989 s (2.8 h) of the recorded 11071 s build (2026-10-11, Idle priority on a shared 16-core laptop; see
`multifile/compile_clean.log`). `BUSYCOQ` must point to the `verify/`
directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo` and `Flip.vo` built.

`probe.v` does three things:

- it re-checks by conversion all 24 entries of T12a's transition table against the machine string (the lines are
  generated from the string, not from the Coq file), and the blank start configuration;
- it prints the definitions the statements use (`arrow`, `F`, `iter`, `T_def`, `JJ`, `ones`, `count1`,
  `sym_val`, `step`, `stepn`, `g0`, `fin`, `Wf`, n1's `score_value`, `fgh`, `f_omega`, `f_omega1`) and the types of
  the main theorems;
- it runs `Print Assumptions` for the five theorems above. All five must say `Closed under the global context`.

There is no single self-contained file for BB12 yet (BB9 and BB10 have one).
