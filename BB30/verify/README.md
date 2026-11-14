# Coq proofs for hydra30 (30 states)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For the machine

```
1RC1L[_---0LY_0RD1RW_0RE0RN_0RF0RF_0RG1RX_0RH1RF_0RI1RI_0LJ1RH_1LK1LU_0LL1LP_1LM0RD_0RD1LT_0RO1RV_1LP1RN_0LQ1LQ_0LR1LP_0LS1LA_1RD1LR_0RQ1LZ_0LT1LM_0RN1RN_1RH0R\_0LY1RF_1LU0LB_0LU1LJ_0LA1LA_0R^1R]_0R\1R\_1LJ1R\
```

(B0 undefined = the halt; `Z` is an ordinary state) it proves:

- `BB30_halt.halt : halts tm c0`: the machine halts from the blank tape;
- `BB30_halt.hardy_bound`: the halting tape holds N ones with `HH (olist hs0) 10 <= N + 2`, and
  `BB30_halt.x0_eq : olist hs0 = powtower 2 (ofin 9)`;
- `BB30_bound.hardy_score`: `FGH (opow (ofin 9)) 10 <= N + 2`;
- `BB30_bound.sigma_lower_bound_w2_9`: `FGH (tower 2) 9 < N`;
- weaker corollaries: FGH (tower 2) 3 < N.

`Ord.v` (ordinals below ε₀ in Cantor normal form, standard fundamental sequences, the fast-growing hierarchy
`FGH`), `Hardy.v` (the Hardy hierarchy `HH`, `hardy_game`) and `HydraOrd.v` (hydras and their ordinals) are
byte-identical to [`../../BB31/verify/multifile/`](../../BB31/verify/multifile/)'s; see
[`../../BB31/verify/README.md`](../../BB31/verify/README.md) for their content. `tower k` = ω↑↑k, `powtower j y` = ω^…^y
with j omegas. `ones c N` says the tape of c is a finite word padded with 0s holding N ones. `probe.v` prints all
of these definitions.

## Files

| file | content |
|---|---|
| `BB302.v`, `Individual302.v` | busycoq instantiated for 30 states (as BB31's, with 30 state constructors). State character c is the constructor q + the spreadsheet column of ord(c) − 65: A..Z → qA..qZ, then `[`, `\`, `]`, `^` → qAA..qAD. |
| `BB30_tm.v` | the transition table, with the machine string in a comment |
| `BB30_rules.v` | pair alphabet, state roles, atomic pair rules |
| `BB30_scan.v`, `BB30_round.v`, `BB30_game.v` | scan lemmas, round lemmas, the game as an instance of `hardy_game` (BB31's files up to comments and names) |
| `BB30_halt.v` | the 2,590-step opening (literal, in chunks of 250 steps), the initial hydra, `hardy_bound`, `halt` |
| `BB30_bound.v` | the FGH statements |
| `Ord.v`, `Hardy.v`, `HydraOrd.v` | shared library (copies of BB31's) |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`probe.v` checks the compiled transition table against the machine string entry by entry (lines generated from
the string, not from the Coq file; rows are fixed-width), prints the definitions the statements use, and runs
`Print Assumptions` on 6 theorems (`halt`, `hardy_bound`, `x0_eq`, `hardy_score`, `sigma_lower_bound_w2_9`, `sigma_lower_bound`): all are closed under the global context. CI job
`bb13-bb14` runs the same script.
