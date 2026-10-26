# Coq proofs for `1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LH1LK` (M12)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (K0 undefined = the halt, `1RZ` in the string) it proves:

- `BB12_M12.halt : halts tm c0`: the machine halts from the blank tape;
- `BB12_M12_bound.score_exact`: the halting tape holds exactly `fst pb2 + snd pb2 / 2 + 3` ones, where `pb2`
  is the explicit pair computed by the run (see `BB12_M12.v`, section "The full run of M12");
- `BB12_M12_bound.sigma_lower_bound_strong`: the halting tape holds N ones with `f_omega2 (f_omega 20) < N + 1`;
- `BB12_M12_bound.sigma_lower_bound_m12`: `f_omega2 (f_omega1 (f_omega1 3)) < N + 1`
  (`sigma_lower_bound`, with `f_omega2 20`, is also in the file).

The fast-growing hierarchy is the standard one, defined in `BB12_M12_bound.v`: `f 0 n = n+1`,
`f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`, `f_omega2 n = f_omega1^n n`.
`ones c N` says that `c`'s tape is a finite word padded with 0s on both sides holding N ones. The machine halts in
state K reading 0, and the halting transition writes 1, so the standard score is N + 1.

## Files

| file | content |
|---|---|
| `BB122.v`, `Individual122.v` | busycoq instantiated for 12 states (byte-identical to `../../verify/multifile/`). The state `L` shadows busycoq's direction `L`, so tables write `TM.L` / `TM.R`. |
| `BB12_M12.v` | the halting proof: configuration families, shift and cascade rules, the maps `W`, `Kc`, `Kd_step`, the run |
| `BB12_M12_bound.v` | the exact score and the lower bounds; imports the halting file unchanged |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (35 s), hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`probe.v` checks the compiled transition table against the machine string entry by entry (lines generated from the
string, not from the Coq file), prints the definitions the statements use, and runs `Print Assumptions` on the four
theorems above: all four are closed under the global context. CI job `bb13-bb14` runs the same script.

Line 1 of `BB12_M12.v` was changed from Argon's original heading, which stated a bound
(`f_(omega+2)(f_(omega+1)(f_(omega+1) 6) / 6)`) that no theorem in the files proves.
