# Coq proofs for hydra32 (32 states)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For the machine

```
1RC1LT_---0LZ_0RD1RU_0RE0RW_0RF0RF_0RG1RS_0RH1RF_0RI1RI_0LJ1RH_1LK1L[_0RL1LO_1RM1RL_0RN1RV_1LJ1RM_0LP1LP_0LQ1LO_0LR1LA_1RD1LQ_0LZ1RF_0LA1LA_1RH0RM_0RM1RM_0RX1RY_1LO1RW_0RW1RW_1L[0LB_0L_1L\_0RD1L]_0LJ1L^_0L[1L__0RP1L`_0L]1LJ
```

(B0 undefined = the halt; `Z` is an ordinary state) it proves:

- `BB32_halt.halt : halts tm c0`: the machine halts from the blank tape;
- `BB32_halt.hardy_bound`: the halting tape holds N ones with `HH (olist hs0) 4 <= N + 2`, and
  `BB32_halt.x0_eq : olist hs0 = powtower 3 (orep (ofin 8) 3 oz)`;
- `BB32_bound.hardy_score`: `FGH a32 4 <= N + 2, a32 = powtower 2 (orep (ofin 8) 3 oz)`;
- `BB32_bound.sigma_lower_bound_w4_8`: `FGH (tower 4) 8 < N`;
- weaker corollaries: FGH (tower 4) 4 < N (`sigma_lower_bound_w4`), FGH (tower 4) 3 < N.

`Ord.v` (ordinals below ε₀ in Cantor normal form, standard fundamental sequences, the fast-growing hierarchy
`FGH`), `Hardy.v` (the Hardy hierarchy `HH`, `hardy_game`) and `HydraOrd.v` (hydras and their ordinals) are
byte-identical to [`../../BB31/verify/multifile/`](../../BB31/verify/multifile/)'s; see
[`../../BB31/verify/README.md`](../../BB31/verify/README.md) for their content. `tower k` = ω↑↑k, `powtower j y` = ω^…^y
with j omegas. `ones c N` says the tape of c is a finite word padded with 0s holding N ones. `probe.v` prints all
of these definitions.

## Files

| file | content |
|---|---|
| `BB322.v`, `Individual322.v` | busycoq instantiated for 32 states (as BB31's, with 32 state constructors). State character c is the constructor q + the spreadsheet column of ord(c) − 65: A..Z → qA..qZ, then `[`, `\`, `]`, `^`, `_`, `` ` `` → qAA..qAF. |
| `BB32_tm.v` | the transition table, with the machine string in a comment |
| `BB32_rules.v` | pair alphabet, state roles, atomic pair rules |
| `BB32_scan.v`, `BB32_round.v`, `BB32_game.v` | scan lemmas, round lemmas, the game as an instance of `hardy_game` (BB31's files up to comments and names) |
| `BB32_halt.v` | the 4,501-step opening (literal, in chunks of 250 steps), the initial hydra, `hardy_bound`, `halt` |
| `BB32_bound.v` | the FGH statements |
| `Ord.v`, `Hardy.v`, `HydraOrd.v` | shared library (copies of BB31's) |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`probe.v` checks the compiled transition table against the machine string entry by entry (lines generated from
the string, not from the Coq file; rows are fixed-width), prints the definitions the statements use, and runs
`Print Assumptions` on 7 theorems (`halt`, `hardy_bound`, `x0_eq`, `hardy_score`, `sigma_lower_bound_w4_8`, `sigma_lower_bound_w4`, `sigma_lower_bound`): all are closed under the global context. CI job
`bb13-bb14` runs the same script.
