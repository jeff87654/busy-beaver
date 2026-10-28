# Coq proofs for `1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LN0LL_0LH1LK_1RZ0LH_0RJ0LI` (M14b)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (M0 undefined = the halt, `1RZ` in the string) it proves:

- `BB14_M14b.halt : halts tm c0`: the machine halts from the blank tape;
- `BB14_M14b_bound.score_exact`: the halting tape holds exactly `fst pa13 + snd pa13 + 5` ones, where `pa13`
  is the explicit pair computed by the run (see `BB14_M14b.v`, section "The 13-round trajectory of M14b");
- `BB14_M14b_bound.sigma_lower_bound`: the halting tape holds N ones with
  `iter 9 f_omega2 (f_omega1 (f_omega1 3)) < N + 1`.

The fast-growing hierarchy is the standard one, defined in `BB14_M14b_bound.v`: `f 0 n = n+1`,
`f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`, `f_omega2 n = f_omega1^n n`; `iter` is
defined in `BB14_M14b.v` (`iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`). `ones c N` says that `c`'s tape is a
finite word padded with 0s on both sides holding N ones. The machine halts in state M reading 0, and the halting
transition writes 1, so the standard score is N + 1.

## Files

| file | content |
|---|---|
| `BB142.v`, `Individual142.v` | busycoq instantiated for 14 states (byte-identical to `../../verify/multifile/`). The state `L` shadows busycoq's direction `L`, so tables write `TM.L` / `TM.R`. |
| `BB14_M14b.v` | the halting proof: configuration families, shift and cascade rules, the reload, the maps `W`, `Kc`, `Kc_full`, `Kd_step`, the residue invariants, the run |
| `BB14_M14b_bound.v` | the exact score and the lower bound; imports the halting file unchanged |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (about 40 s), hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table against the machine string entry by entry
(lines generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the three theorems above: all three are closed
under the global context. CI job `bb13-bb14` runs the same script.

The four `.v` files are Argon's, unchanged.
