# Coq proofs for `1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LN1RF_1LJ0RA_1RA0LH_1LG1LH_1RK0LM_1RZ0LE_0LE0RJ_1LH1LM_0LH0LL_0LG1LN` (M14)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (J0 undefined = the halt, `1RZ` in the string) it proves:

- `BB14_M14.halt : halts tm c0` -- the machine halts from the blank tape;
- `BB14_M14_bound.score_exact` -- the halting tape holds exactly `fst pa3 + snd pa3 + 2` ones, where `pa3`
  is the explicit pair computed by the run (see `BB14_M14.v`);
- `BB14_M14_bound.sigma_lower_bound` -- the halting tape holds N ones with `f_omega2 (f_omega2 (f_omega2 15)) < N + 1`;
- `BB14_M14_bound.sigma_lower_bound_strong` -- `f_omega2 (f_omega2 (iter 15 f_omega1 (f_omega 21))) < N + 1`.

The fast-growing hierarchy is the standard one, defined in `BB14_M14_bound.v`: `f 0 n = n+1`,
`f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`, `f_omega2 n = f_omega1^n n`.
`ones c N` says that `c`'s tape is a finite word padded with 0s on both sides holding N ones. The machine halts in
state J0 reading 0, and the halting transition writes 1, so the standard score is N + 1.

## Files

| file | content |
|---|---|
| `BB142.v`, `Individual142.v` | busycoq instantiated for 14 states (mirrors `BB122.v` of `../../BB12/`). The state `L` shadows busycoq's direction `L`, so tables write `TM.L` / `TM.R`. |
| `BB14_M14.v` | the halting proof: configuration families, shift and cascade rules, the pair maps, the run |
| `BB14_M14_bound.v` | the exact score and the lower bounds; imports the halting file unchanged |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

This compiles the 4 files in dependency order (about 30 s) and then runs `probe.v`. `BUSYCOQ` must point to the
`verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo` and `Flip.vo` built. The
GitHub workflow (`.github/workflows/coq.yml`, job `bb13-bb14`) runs the same build and probe on every push.

`probe.v` does three things:

- it re-checks by conversion all 28 entries of M14's transition table against the machine string (the lines are
  generated from the string, not from the Coq file), and the blank start configuration;
- it prints the definitions the statements use (`iter`, `f`, `f_omega`, `f_omega1`, `f_omega2`, `sym_val`,
  `count1`, `ones`) and the types of the main theorems;
- it runs `Print Assumptions` for the four theorems above. All four must say `Closed under the global context`.

## Provenance

The four `.v` files are Argon's (see the write-up, section 5), unchanged except line 1 of `BB14_M14.v`. Argon's
heading comment there stated a stronger bound than the one proved (`f_(omega+2)^3(16)`); it now
states the bound that `BB14_M14_bound.v` proves. `probe.v`, `compile_clean.sh` and `_CoqProject` were added here.
